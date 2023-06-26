from itertools import count
from typing import Optional, List, Dict, Tuple, Set, Callable, Any, TYPE_CHECKING


import networkx

import claripy

from ...sim_options import NO_CROSS_INSN_OPT, SYMBOL_FILL_UNCONSTRAINED_MEMORY, SYMBOL_FILL_UNCONSTRAINED_REGISTERS, SIMPLIFY_CONSTRAINTS
from ...state_plugins.inspect import BP_BEFORE, BP_AFTER, BP
from ..analysis import Analysis, AnalysesHub

if TYPE_CHECKING:
    from angr import SimState
    from angr.knowledge_plugins.functions import Function
    from .abstract_state import AbstractStateFields


class ConstraintLogger:
    """
    Logs constraints and where they are created via the on_adding_constraints callback.
    """
    def __init__(self, mapping: Dict[claripy.ast.Base,Tuple[int,int]]):
        self.mapping = mapping

    def on_adding_constraints(self, state: 'SimState'):
        added_constraints = state._inspect_getattr('added_constraints', None)
        if not (len(added_constraints) == 1 and (
                claripy.is_true(added_constraints[0]) or
                claripy.is_false(added_constraints[0]))):
            for constraint in added_constraints:
                self.mapping[constraint] = state.scratch.irsb.addr, state.scratch.stmt_idx


class ExpressionLogger:
    """
    Logs symbolic expressions and where they are created via the on_register_write callback.
    """
    def __init__(self, mapping: Dict[claripy.ast.Base,Tuple[int,int]], variables: Set[str]):
        self.mapping = mapping
        self.variables: Set[str] = variables if variables else set()

    def on_memory_read(self, state: 'SimState'):
        expr = state._inspect_getattr("mem_read_expr", None)
        if expr is not None and expr.symbolic and expr.variables.intersection(self.variables):
            mem_read_addr = state._inspect_getattr("mem_read_address", None)
            if mem_read_addr is not None:
                if isinstance(mem_read_addr, int):
                    self.mapping[expr] = mem_read_addr
                elif not mem_read_addr.symbolic:
                    self.mapping[expr] = mem_read_addr._model_concrete.value

    def on_register_write(self, state: 'SimState'):
        expr = state._inspect_getattr('reg_write_expr', None)
        if expr is not None and expr.symbolic and expr.variables.intersection(self.variables):
            if expr not in self.mapping:
                # do not overwrite an existing source - it might have been from a memory read, which is the real source...
                self.mapping[expr] = state.scratch.irsb.addr, state.scratch.stmt_idx


class DefinitionNode:
    def __init__(self, variable: str, block_addr: int, stmt_idx: int):
        self.variable = variable
        self.block_addr = block_addr
        self.stmt_idx = stmt_idx

    def __eq__(self, other):
        return (
                isinstance(other, DefinitionNode)
                and self.variable == other.variable
                and self.block_addr == other.block_addr
        )

    def __hash__(self):
        return hash((DefinitionNode, self.variable, self.block_addr, self.stmt_idx))

    def __repr__(self):
        return f"{self.variable}@{self.block_addr:#x}:{self.stmt_idx}"


class SliceGenerator:
    def __init__(self, symbolic_exprs: Set[claripy.ast.Base], bp: Optional[BP]=None):
        self.bp: Optional[BP] = bp
        self.symbolic_exprs = symbolic_exprs
        self.expr_variables = set()

        # FIXME: The algorithm is hackish and incorrect. We should fix it later.
        self._last_statements = { }
        self.slice = networkx.DiGraph()

        for expr in self.symbolic_exprs:
            self.expr_variables |= expr.variables

        if self.bp is not None:
            self.bp.action = self._examine_expr

    def install_expr_hook(self, state: 'SimState') -> BP:
        bp = BP(when=BP_AFTER, enabled=False, action=self._examine_expr)
        state.inspect.add_breakpoint('expr', bp)
        self.bp = bp
        return bp

    def _examine_expr(self, state: 'SimState'):
        expr = state._inspect_getattr('expr_result', None)
        if state.solver.symbolic(expr) and expr.variables.intersection(self.expr_variables):

            variables = expr.variables
            curr_loc = state.scratch.irsb.addr, state.scratch.stmt_idx
            for v in variables:
                pred = self._last_statements.get(v, None)
                if pred is not None:
                    self.slice.add_edge(DefinitionNode(v, pred[0], pred[1]),
                                        DefinitionNode(v, curr_loc[0], curr_loc[1]))
                self._last_statements[v] = curr_loc
            # print(expr, state.scratch.irsb.statements[state.scratch.stmt_idx])


class StateGraphRecoveryAnalysis(Analysis):
    """
    Traverses a function and derive a state graph with respect to given variables.
    """
    def __init__(self, func: 'Function', fields: 'AbstractStateFields', software: str,
                 time_addr: int, rollsensor_addr: int = None,
                 init_state: Optional['SimState']=None, init_variables: Dict = None,
                 switch_on: Optional[Callable]=None,
                 printstate: Optional[Callable]=None,
                 config_vars: Optional[Set[claripy.ast.Base]]=None,
                 patch_callback: Optional[Callable]=None,
                 state_id_addr: int = None):
        self.func = func
        self.fields = fields
        self.config_vars = config_vars if config_vars is not None else set()
        self.software = software
        self.init_state = init_state
        self.init_variables = init_variables
        self._switch_on = switch_on
        self._ret_trap: int = 0x1f37ff4a
        self.printstate = printstate
        self.patch_callback = patch_callback
        self.state_id_addr = state_id_addr

        self._time_addr = time_addr
        # self._temp_addr = temp_addr
        self._rollsensor_addr = rollsensor_addr
        self._tv_sec_var = None
        # self._temperature = None
        self._rollsensor = None
        self.state_graph = None
        self._expression_source = {}

        self.traverse()

    class Deltas:
        """
        logs state transition and delta information during delta discovery.
        """
        def __init__(self, curr_id: int, next_id: int, state: 'SimState', delta: claripy.ast.bv):
            self.curr_id = curr_id
            self.next_id = next_id
            self.state = state
            self.delta = delta

            self.steps = []
            self.constraint = None
            self.constraint_sources = []
            self.new_value = None

            # self.same_range = False

        def is_changed(self) -> bool:
            return self.curr_id == self.next_id



    def traverse(self):

        # create an empty state graph
        self.state_graph = networkx.DiGraph()

        # make the initial state
        init_state = self._initialize_state(init_state=self.init_state)

        symbolic_input_fields = self._symbolize_input_fields(init_state)
        symbolic_time_counters = self._symbolize_timecounter(init_state)
        symbolic_rollsensor = self._symbolize_rollsensor(init_state)
        # if self._temp_addr is not None:
        #     symbolic_temperature = self._symbolize_temp(init_state)

        # setup inspection points to catch where expressions are created
        all_vars = set(symbolic_input_fields.values())
        all_vars |= set(symbolic_time_counters.values())
        all_vars |= set(symbolic_rollsensor.values())
        # if self._temp_addr is not None:
        #     all_vars |= set(symbolic_temperature.values())
        all_vars |= self.config_vars
        slice_gen = SliceGenerator(all_vars, bp=None)
        expression_bp = slice_gen.install_expr_hook(init_state)

        # setup inspection points to catch where expressions are written to registers
        expression_logger = ExpressionLogger(self._expression_source, { v.args[0] for v in all_vars })
        regwrite_bp = BP(when=BP_BEFORE, enabled=True, action=expression_logger.on_register_write)
        init_state.inspect.add_breakpoint('reg_write', regwrite_bp)
        memread_bp = BP(when=BP_AFTER, enabled=True, action=expression_logger.on_memory_read)
        init_state.inspect.add_breakpoint('mem_read', memread_bp)

        # Abstract state ID counter
        abs_state_id_ctr = count(0)

        abs_state = self.fields.generate_abstract_state(init_state)
        abs_state_id = next(abs_state_id_ctr)
        self.state_graph.add_node((('NODE_CTR', abs_state_id),) + abs_state, outvars = dict(abs_state))
        state_queue = [(init_state, abs_state_id, abs_state, None, None, None, None, None, None, None)]
        if self._switch_on is None:
            countdown_timer = 0
            switched_on = True

            # time_delta_and_sources = self._discover_time_deltas(init_state)
            #
            # for delta, constraint, source in time_delta_and_sources:
            #     if source is None:
            #         block_addr, stmt_idx = -1, -1
            #     else:
            #         block_addr, stmt_idx = source
            #     print(f"[.] Discovered a new time interval {delta} defined at {block_addr:#x}:{stmt_idx}")
            #
            #
            # rollsensor_delta_and_sources = self._discover_rollsensor_deltas(init_state)
            #
            # if rollsensor_delta_and_sources or time_delta_and_sources:
            #
            #     if any(x.steps for x in rollsensor_delta_and_sources):
            #         # import ipdb; ipdb.set_trace()
            #         for rollsensor_object in rollsensor_delta_and_sources:
            #             # append two states in queue
            #
            #
            #             new_state = self._initialize_state(init_state=init_state)
            #
            #             # re-symbolize input fields, time counters, and update slice generator
            #             symbolic_input_fields = self._symbolize_input_fields(new_state)
            #             symbolic_time_counters = self._symbolize_timecounter(new_state)
            #             symbolic_rollsensor = self._symbolize_rollsensor(new_state)
            #             all_vars = set(symbolic_input_fields.values())
            #             all_vars |= set(symbolic_time_counters.values())
            #             all_vars |= set(symbolic_rollsensor.values())
            #             all_vars |= self.config_vars
            #             slice_gen = SliceGenerator(all_vars, bp=expression_bp)
            #             state_queue.append((
            #                    new_state, abs_state_id, abs_state, None, None, None, None,
            #                    rollsensor_object.new_value, rollsensor_object.constraint, rollsensor_object.constraint_sources))
            #
            #             # fixme: using new Delta objects
            #             if time_delta_and_sources:
            #                 # print(time_delta_constraint)
            #                 for time_delta, time_constraint, time_src in time_delta_and_sources:
            #                     # append state satisfy constraint
            #                     new_state = self._initialize_state(init_state=init_state)
            #
            #                     # re-symbolize input fields, time counters, and update slice generator
            #                     symbolic_input_fields = self._symbolize_input_fields(new_state)
            #                     symbolic_time_counters = self._symbolize_timecounter(new_state)
            #                     symbolic_rollsensor = self._symbolize_rollsensor(new_state)
            #                     all_vars = set(symbolic_input_fields.values())
            #                     all_vars |= set(symbolic_time_counters.values())
            #                     all_vars |= set(symbolic_rollsensor.values())
            #                     all_vars |= self.config_vars
            #                     slice_gen = SliceGenerator(all_vars, bp=expression_bp)
            #                     state_queue.append((new_state, abs_state_id, abs_state, None, time_delta, time_constraint, time_src,
            #                                         rollsensor_object.new_value, rollsensor_object.constraint, rollsensor_object.constraint_sources))
            #
            #                     # append state not satisfy constraint
            #                     new_state = self._initialize_state(init_state=init_state)
            #
            #                     # re-symbolize input fields, time counters, and update slice generator
            #                     symbolic_input_fields = self._symbolize_input_fields(new_state)
            #                     symbolic_time_counters = self._symbolize_timecounter(new_state)
            #                     symbolic_rollsensor = self._symbolize_rollsensor(new_state)
            #                     all_vars = set(symbolic_input_fields.values())
            #                     all_vars |= set(symbolic_time_counters.values())
            #                     all_vars |= set(symbolic_rollsensor.values())
            #                     all_vars |= self.config_vars
            #                     slice_gen = SliceGenerator(all_vars, bp=expression_bp)
            #                     state_queue.append((new_state, abs_state_id, abs_state, None, time_delta, time_constraint, time_src, None, None, None))
            #
            #     # only discover time delta
            #     # fixme: using new Delta objects
            #     else:
            #         for time_delta, time_constraint, time_src in time_delta_and_sources:
            #             new_state = self._initialize_state(init_state=init_state)
            #
            #             # re-symbolize input fields, time counters, and update slice generator
            #             symbolic_input_fields = self._symbolize_input_fields(new_state)
            #             symbolic_time_counters = self._symbolize_timecounter(new_state)
            #             all_vars = set(symbolic_input_fields.values())
            #             all_vars |= set(symbolic_time_counters.values())
            #             all_vars |= set(symbolic_rollsensor.values())
            #             # if self._temp_addr is not None:
            #             #     symbolic_temperature = self._symbolize_temp(new_state)
            #             #     all_vars |= set(symbolic_temperature.values())
            #             all_vars |= self.config_vars
            #             slice_gen = SliceGenerator(all_vars, bp=expression_bp)
            #             state_queue.append((new_state, abs_state_id, abs_state, None, time_delta, time_constraint, time_src, None, None, None))
            #
            # else:
            #     # if time_delta is None and prev_abs_state == abs_state:
            #     #     continue
            #     new_state = self._initialize_state(init_state=init_state)
            #
            #     # re-symbolize input fields, time counters, and update slice generator
            #     symbolic_input_fields = self._symbolize_input_fields(new_state)
            #     symbolic_time_counters = self._symbolize_timecounter(new_state)
            #
            #     all_vars = set(symbolic_input_fields.values())
            #     all_vars |= set(symbolic_time_counters.values())
            #     all_vars |= set(symbolic_rollsensor.values())
            #     # if self._temp_addr is not None:
            #     #     symbolic_temperature = self._symbolize_temp(new_state)
            #     #     all_vars |= set(symbolic_temperature.values())
            #     all_vars |= self.config_vars
            #     slice_gen = SliceGenerator(all_vars, bp=expression_bp)
            #
            #     state_queue.append((new_state, abs_state_id, abs_state, None, None, None, None, None, None, None))

        else:
            countdown_timer = 2  # how many iterations to execute before switching on
            switched_on = False

        known_transitions = list()
        known_states = dict()
        time_delta_and_sources = {}
        # temp_delta_and_sources = {}
        rollsensor_delta_and_sources = {}

        absstate_to_slice = { }
        while state_queue:
            prev_state, prev_abs_state_id, prev_abs_state, prev_prev_abs, time_delta, time_delta_constraint, time_delta_src, rollsensor_delta, rollsensor_delta_constraint, rollsensor_delta_src = state_queue.pop(0)
            if time_delta is None:
                pass
            else:
                # advance the time stamp as required
                self._advance_timecounter(prev_state, time_delta)

            if rollsensor_delta is None:
                pass
            else:
                # advance the time stamp as required
                self._advance_rollsensor(prev_state, rollsensor_delta)

            # if temp_delta is None:
            #     pass
            # else:
            #     # advance the temperature stamp as required
            #     self._advance_temp(prev_state, temp_delta)

            # symbolically trace the state
            expression_bp.enabled = True
            next_state = self._traverse_one(prev_state)

            # print(f"motor throttle in {next_state.memory.load(0xc00042f0 + 0x28, 4, endness=self.project.arch.memory_endness).raw_to_fp()}")
            # print(f"motor throttle out {next_state.memory.load(0xc00042f0+0x2c,4, endness=self.project.arch.memory_endness).raw_to_fp()}")
            # import ipdb; ipdb.set_trace()
            expression_bp.enabled = False

            abs_state = self.fields.generate_abstract_state(next_state)
            abs_state += (('time_delta', time_delta),
                          # ('tdc', time_delta_constraint),
                          # ('td_src', time_delta_src),
                          # ('temp_delta', temp_delta),
                          # ('temp_src', temp_delta_src)
                          ('rollsensor_delta', rollsensor_delta),
                          # ('rollsensor_src', rollsensor_delta_src)
                          )
                        # TODO: remove values in nodes, Now keep them for debug purpose
                        # TODO: should we add source back?

            if switched_on:
                if abs_state in known_states.keys():
                    abs_state_id = known_states[abs_state]
                else:
                    abs_state_id = next(abs_state_id_ctr)
                    known_states[abs_state] = abs_state_id
            else:
                abs_state_id = next(abs_state_id_ctr)
            import pprint
            print("[+] Discovered a new abstract state:")
            if self.printstate is None:
                pprint.pprint(abs_state)
            else:
                self.printstate(abs_state)
            absstate_to_slice[abs_state] = slice_gen.slice
            print("[.] There are %d nodes in the slice." % len(slice_gen.slice))

            transition = (prev_prev_abs, prev_abs_state, abs_state)
            if switched_on and transition in known_transitions:
                continue

            known_transitions.append(transition)
            self.state_graph.add_node((('NODE_CTR', abs_state_id),) + abs_state, outvars=dict(abs_state))

            self.state_graph.add_edge((('NODE_CTR', prev_abs_state_id),) + prev_abs_state,
                                      (('NODE_CTR', abs_state_id),) + abs_state,
                                      time_delta=time_delta,
                                      time_delta_constraint=time_delta_constraint,
                                      time_delta_src=time_delta_src,
                                      # temp_delta=temp_delta,
                                      # temp_delta_constraint=temp_delta_constraint,
                                      # temp_delta_src=temp_delta_src,
                                      rollsensor_delta=rollsensor_delta,
                                      rollsensor_delta_constraint=rollsensor_delta_constraint,
                                      rollsensor_delta_src=rollsensor_delta_src,
                                      label=f'time_delta_constraint={time_delta_constraint},\nrollsensor_delta_constraint={rollsensor_delta_constraint}'
                                      )

            # discover time deltas
            if not switched_on and self._switch_on is not None:
                if countdown_timer > 0:
                    print("[.] Pre-heat... %d" % countdown_timer)
                    countdown_timer -= 1
                    new_state = self._initialize_state(init_state=next_state)
                    state_queue.append((new_state, abs_state_id, abs_state, None, 1, None, None, None, None, None))
                    continue
                else:
                    print("[.] Switch on.")
                    self._switch_on(next_state)
                    if self.patch_callback is not None:
                        print("[.] Applying patches...")
                        self.patch_callback(next_state)
                    switched_on = True
                    time_delta_and_sources = {}
                    # temp_delta_and_sources = {}
                    rollsensor_delta_and_sources = {}
                    prev_abs_state = None
                    # state_queue.append((new_state, abs_state_id, abs_state, None, None, None, None, None, None))
            else:
                time_delta_and_sources = self._discover_time_deltas(next_state)

                for delta, constraint, source in time_delta_and_sources:
                    if source is None:
                        block_addr, stmt_idx = -1, -1
                    else:
                        block_addr, stmt_idx = source
                    print(f"[.] Discovered a new time interval {delta} defined at {block_addr:#x}:{stmt_idx}")
                # if self._temp_addr is not None:
                #     temp_delta_and_sources = self._discover_temp_deltas(next_state)
                #     for delta, constraint, source in temp_delta_and_sources:
                #         if source is None:
                #             block_addr, stmt_idx = -1, -1
                #         else:
                #             block_addr, stmt_idx = source
                #         print(f"[.] Discovered a new temperature {delta} defined at {block_addr:#x}:{stmt_idx}")
                if self._rollsensor_addr is not None:
                    rollsensor_delta_and_sources = self._discover_rollsensor_deltas(next_state)
                    # fixme later when i added original step_info
                    # for delta, constraint, source in rollsensor_delta_and_sources:
                    #     if source is None:
                    #         block_addr, stmt_idx = -1, -1
                    #     else:
                    #         block_addr, stmt_idx = source
                    #     print(f"[.] Discovered a new rollsensor {delta} defined at {block_addr:#x}:{stmt_idx}")

            # if temp_delta_and_sources or time_delta_and_sources:
            #
            #     if temp_delta_and_sources:
            #
            #         for temp_delta, temp_constraint, temp_src in temp_delta_and_sources:
            #             # append two states in queue
            #             op = temp_constraint.args[0].op
            #             prev = next_state.memory.load(self._temp_addr, 8, endness=self.project.arch.memory_endness).raw_to_fp()
            #             prev_temp = next_state.solver.eval(prev)
            #             if op in ['fpLEQ', 'fpLT', 'fpGEQ', 'fpGT']:
            #                 if prev_temp < temp_delta:
            #                     delta0, temp_constraint0, temp_src0 = None, None, None
            #                     delta1, temp_constraint1, temp_src1 = temp_delta + 1.0, temp_constraint, temp_src
            #
            #                     new_state = self._initialize_state(init_state=next_state)
            #
            #                     # re-symbolize input fields, time counters, and update slice generator
            #                     symbolic_input_fields = self._symbolize_input_fields(new_state)
            #                     symbolic_time_counters = self._symbolize_timecounter(new_state)
            #                     symbolic_temperature = self._symbolize_temp(new_state)
            #                     all_vars = set(symbolic_input_fields.values())
            #                     all_vars |= set(symbolic_time_counters.values())
            #                     all_vars |= set(symbolic_temperature.values())
            #                     all_vars |= self.config_vars
            #                     slice_gen = SliceGenerator(all_vars, bp=expression_bp)
            #                     state_queue.append((new_state, abs_state_id, abs_state, prev_abs_state, None, None, None, delta1,
            #                                         temp_constraint1, temp_src1))
            #                 elif prev_temp > temp_delta:
            #                     delta0, temp_constraint0, temp_src0 = temp_delta - 1.0, temp_constraint, temp_src
            #                     delta1, temp_constraint1, temp_src1 = None, None, None
            #
            #                     new_state = self._initialize_state(init_state=next_state)
            #
            #                     # re-symbolize input fields, time counters, and update slice generator
            #                     symbolic_input_fields = self._symbolize_input_fields(new_state)
            #                     symbolic_time_counters = self._symbolize_timecounter(new_state)
            #                     symbolic_temperature = self._symbolize_temp(new_state)
            #                     all_vars = set(symbolic_input_fields.values())
            #                     all_vars |= set(symbolic_time_counters.values())
            #                     all_vars |= set(symbolic_temperature.values())
            #                     all_vars |= self.config_vars
            #                     slice_gen = SliceGenerator(all_vars, bp=expression_bp)
            #                     state_queue.append((new_state, abs_state_id, abs_state, prev_abs_state, None, None, None, delta0,
            #                                         temp_constraint0, temp_src0))
            #                 else:
            #                     import ipdb; ipdb.set_trace()
            #
            #             elif op in ['fpEQ']:
            #                 # import ipdb; ipdb.set_trace()
            #                 new_state = self._initialize_state(init_state=next_state)
            #
            #                 # re-symbolize input fields, time counters, and update slice generator
            #                 symbolic_input_fields = self._symbolize_input_fields(new_state)
            #                 symbolic_time_counters = self._symbolize_timecounter(new_state)
            #                 symbolic_temperature = self._symbolize_temp(new_state)
            #                 all_vars = set(symbolic_input_fields.values())
            #                 all_vars |= set(symbolic_time_counters.values())
            #                 all_vars |= set(symbolic_temperature.values())
            #                 all_vars |= self.config_vars
            #                 slice_gen = SliceGenerator(all_vars, bp=expression_bp)
            #                 state_queue.append((new_state, abs_state_id, abs_state, prev_abs_state, None, None, None, temp_delta, temp_constraint, temp_src))
            #                 continue

            if rollsensor_delta_and_sources or time_delta_and_sources:

                if any(x.steps for x in rollsensor_delta_and_sources):
                    # import ipdb; ipdb.set_trace()
                    for rollsensor_object in rollsensor_delta_and_sources:
                        # append two states in queue


                        new_state = self._initialize_state(init_state=next_state)

                        # re-symbolize input fields, time counters, and update slice generator
                        symbolic_input_fields = self._symbolize_input_fields(new_state)
                        symbolic_time_counters = self._symbolize_timecounter(new_state)
                        symbolic_rollsensor = self._symbolize_rollsensor(new_state)
                        all_vars = set(symbolic_input_fields.values())
                        all_vars |= set(symbolic_time_counters.values())
                        all_vars |= set(symbolic_rollsensor.values())
                        all_vars |= self.config_vars
                        slice_gen = SliceGenerator(all_vars, bp=expression_bp)
                        state_queue.append((
                               new_state, abs_state_id, abs_state, prev_abs_state, None, None, None,
                               rollsensor_object.new_value, rollsensor_object.constraint, rollsensor_object.constraint_sources))


                        # elif op in ['fpEQ']:
                        #     # import ipdb; ipdb.set_trace()
                        #     new_state = self._initialize_state(init_state=next_state)
                        #
                        #     # re-symbolize input fields, time counters, and update slice generator
                        #     symbolic_input_fields = self._symbolize_input_fields(new_state)
                        #     symbolic_time_counters = self._symbolize_timecounter(new_state)
                        #     symbolic_temperature = self._symbolize_temp(new_state)
                        #     all_vars = set(symbolic_input_fields.values())
                        #     all_vars |= set(symbolic_time_counters.values())
                        #     all_vars |= set(symbolic_temperature.values())
                        #     all_vars |= self.config_vars
                        #     slice_gen = SliceGenerator(all_vars, bp=expression_bp)
                        #     state_queue.append((new_state, abs_state_id, abs_state, prev_abs_state, None,
                        #                         None, None, temp_delta, temp_constraint, temp_src))
                        #     continue

                        # fixme: using new Delta objects
                        if time_delta_and_sources:
                            # print(time_delta_constraint)
                            for time_delta, time_constraint, time_src in time_delta_and_sources:
                                # append state satisfy constraint
                                new_state = self._initialize_state(init_state=next_state)

                                # re-symbolize input fields, time counters, and update slice generator
                                symbolic_input_fields = self._symbolize_input_fields(new_state)
                                symbolic_time_counters = self._symbolize_timecounter(new_state)
                                symbolic_rollsensor = self._symbolize_rollsensor(new_state)
                                all_vars = set(symbolic_input_fields.values())
                                all_vars |= set(symbolic_time_counters.values())
                                all_vars |= set(symbolic_rollsensor.values())
                                all_vars |= self.config_vars
                                slice_gen = SliceGenerator(all_vars, bp=expression_bp)
                                state_queue.append((new_state, abs_state_id, abs_state, prev_abs_state, time_delta, time_constraint, time_src,
                                                    rollsensor_object.new_value, rollsensor_object.constraint, rollsensor_object.constraint_sources))

                                # append state not satisfy constraint
                                new_state = self._initialize_state(init_state=next_state)

                                # re-symbolize input fields, time counters, and update slice generator
                                symbolic_input_fields = self._symbolize_input_fields(new_state)
                                symbolic_time_counters = self._symbolize_timecounter(new_state)
                                symbolic_rollsensor = self._symbolize_rollsensor(new_state)
                                all_vars = set(symbolic_input_fields.values())
                                all_vars |= set(symbolic_time_counters.values())
                                all_vars |= set(symbolic_rollsensor.values())
                                all_vars |= self.config_vars
                                slice_gen = SliceGenerator(all_vars, bp=expression_bp)
                                state_queue.append((new_state, abs_state_id, abs_state, prev_abs_state, time_delta, time_constraint, time_src, None, None, None))

                # only discover time delta
                # fixme: using new Delta objects
                else:
                    for time_delta, time_constraint, time_src in time_delta_and_sources:
                        new_state = self._initialize_state(init_state=next_state)

                        # re-symbolize input fields, time counters, and update slice generator
                        symbolic_input_fields = self._symbolize_input_fields(new_state)
                        symbolic_time_counters = self._symbolize_timecounter(new_state)
                        all_vars = set(symbolic_input_fields.values())
                        all_vars |= set(symbolic_time_counters.values())
                        all_vars |= set(symbolic_rollsensor.values())
                        # if self._temp_addr is not None:
                        #     symbolic_temperature = self._symbolize_temp(new_state)
                        #     all_vars |= set(symbolic_temperature.values())
                        all_vars |= self.config_vars
                        slice_gen = SliceGenerator(all_vars, bp=expression_bp)
                        state_queue.append((new_state, abs_state_id, abs_state, prev_abs_state, time_delta, time_constraint, time_src, None, None, None))

            else:
                # if time_delta is None and prev_abs_state == abs_state:
                #     continue
                new_state = self._initialize_state(init_state=next_state)

                # re-symbolize input fields, time counters, and update slice generator
                symbolic_input_fields = self._symbolize_input_fields(new_state)
                symbolic_time_counters = self._symbolize_timecounter(new_state)

                all_vars = set(symbolic_input_fields.values())
                all_vars |= set(symbolic_time_counters.values())
                all_vars |= set(symbolic_rollsensor.values())
                # if self._temp_addr is not None:
                #     symbolic_temperature = self._symbolize_temp(new_state)
                #     all_vars |= set(symbolic_temperature.values())
                all_vars |= self.config_vars
                slice_gen = SliceGenerator(all_vars, bp=expression_bp)

                state_queue.append((new_state, abs_state_id, abs_state, prev_abs_state, None, None, None, None, None, None))

        # TODO: put this part in a function?
        # check if any nodes need to be divided
        for state_node in list(self.state_graph):
            predecessors = list(self.state_graph.predecessors(state_node))
            if len(predecessors) > 1:
                nin = len(predecessors)
                nout = len(list(self.state_graph.successors(state_node)))
                state_edge = list()
                for edge in known_transitions:
                    if state_node[1:] == edge[1]:
                        state_edge.append(edge)
                ntrans = len(state_edge)
                if ntrans == nin * nout:
                    continue
                else:
                    for pre_node in predecessors:
                        new_id = next(abs_state_id_ctr)
                        pre_edge_data = self.state_graph.get_edge_data(pre_node, state_node)
                        self.state_graph.add_edge(pre_node,
                                                  (('NODE_CTR', new_id),) + state_node[1:],
                                                  time_delta=pre_edge_data['time_delta'],
                                                  time_delta_constraint=pre_edge_data['time_delta_constraint'],
                                                  time_delta_src=pre_edge_data['time_delta_src'],
                                                  # temp_delta=pre_edge_data['temp_delta'],
                                                  # temp_delta_constraint=pre_edge_data['temp_delta_constraint'],
                                                  # temp_delta_src=pre_edge_data['temp_delta_src'],
                                                  rollsensor_delta=rollsensor_delta,
                                                  rollsensor_delta_constraint=rollsensor_delta_constraint,
                                                  rollsensor_delta_src=rollsensor_delta_src,
                                                  label=f'time_delta_constraint={time_delta_constraint},\nrollsensor_delta_constraint={rollsensor_delta_constraint}'
                                                  )
                        suc_nodes = [edge[2] for edge in state_edge if edge[0] == pre_node[1:] ]
                        for suc_node in suc_nodes:
                            suc_id = known_states[suc_node]
                            suc_edge_data = self.state_graph.get_edge_data(state_node, ((('NODE_CTR',suc_id),) + suc_node))
                            self.state_graph.add_edge((('NODE_CTR', new_id),) + state_node[1:],
                                                      (('NODE_CTR', suc_id),) + suc_node,
                                                      time_delta=suc_edge_data['time_delta'],
                                                      time_delta_constraint=suc_edge_data['time_delta_constraint'],
                                                      time_delta_src=suc_edge_data['time_delta_src'],
                                                      # temp_delta=suc_edge_data['temp_delta'],
                                                      # temp_delta_constraint=suc_edge_data['temp_delta_constraint'],
                                                      # temp_delta_src=suc_edge_data['temp_delta_src'],
                                                      rollsensor_delta=rollsensor_delta,
                                                      rollsensor_delta_constraint=rollsensor_delta_constraint,
                                                      rollsensor_delta_src=rollsensor_delta_src,
                                                      label=f'time_delta_constraint={time_delta_constraint},\nrollsensor_delta_constraint={rollsensor_delta_constraint}'
                                                      )
                    self.state_graph.remove_node(state_node)

    def _discover_time_deltas(self, state: 'SimState') -> List[Tuple[int,claripy.ast.Base,Tuple[int,int]]]:
        """
        Discover all possible time intervals that may be required to transition the current state to successor states.

        :param state:   The current initial state.
        :return:        A list of ints where each int represents the required interval in number of seconds.
        """

        state = self._initialize_state(state)
        time_deltas = self._symbolically_advance_timecounter(state)
        # setup inspection points to catch where comparison happens
        constraint_source = { }
        constraint_logger = ConstraintLogger(constraint_source)
        bp_0 = BP(when=BP_BEFORE, enabled=True, action=constraint_logger.on_adding_constraints)
        state.inspect.add_breakpoint('constraints', bp_0)

        next_state = self._traverse_one(state)
        # import ipdb; ipdb.set_trace()
        # detect required time delta
        # TODO: Extend it to more than just seconds
        steps: List[Tuple[int,claripy.ast.Base,Tuple[int,int]]] = [ ]
        if time_deltas:
            for delta in time_deltas:
                for constraint in next_state.solver.constraints:
                    original_constraint = constraint
                    # attempt simplification if this constraint has both config variables and time delta variables
                    if any(x.args[0] in constraint.variables for x in self.config_vars) and delta.args[0] in constraint.variables:
                        simplified_constraint, self._expression_source = self._simplify_constraint(constraint,
                                                                                                   self._expression_source)
                        if simplified_constraint is not None:
                            constraint = simplified_constraint

                    if constraint.op == "__eq__" and constraint.args[0].op == "Extract" and constraint.args[1].op == "BVV" and constraint.args[1].args[0] == 0 and delta.args[0] in constraint.variables:
                        # < Bool tv_sec_4966_32[11:0] <= 0x9c4 >, < Bool tv_sec_4966_32[31:12] == 0x0 > -----> tv_sec_4966_32 <= 0x9c4
                        # import ipdb; ipdb.set_trace()
                        cons = [con for con in next_state.solver.constraints if len(con.variables) == 2 and len(con.args) == 2]
                        if cons:
                            left = cons[0].args[0].args[0].args[2] + cons[0].args[0].args[1].args[2]
                            constraint = claripy.ops.ULE(left, claripy.BVV(cons[0].args[1].args[0], cons[0].args[0].args[0].args[2].length))
                            step = constraint.args[1].args[0]
                            if step != 0:
                                steps.append((
                                    step,
                                    constraint,
                                    constraint_source.get(original_constraint, None),
                                ))
                                continue

                    if constraint.op == "__eq__" and constraint.args[0] is delta:
                        continue
                    elif constraint.op in ['ULE']:  # arduino arm32
                        if constraint.args[0].args[1] is delta:
                            if constraint.args[1].args[0].op == 'BVV':
                                step = constraint.args[1].args[0].args[0]
                                if step != 0:
                                    steps.append((
                                        step,
                                        constraint,
                                        constraint_source.get(original_constraint, None),
                                    ))
                                    continue

                    elif constraint.op == "__ne__":
                        if constraint.args[0] is delta:     # amd64
                            # found a potential step
                            if constraint.args[1].op == 'BVV':
                                step = constraint.args[1]._model_concrete.value
                                if step != 0:
                                    steps.append((
                                        step,
                                        constraint,
                                        constraint_source.get(original_constraint, None),
                                    ))
                                    continue
                            else:
                                # attempt to evaluate the right-hand side
                                values = state.solver.eval_upto(constraint.args[1], 2)
                                if len(values) == 1:
                                    # it has a single value!
                                    step = values[0]
                                    if step != 0:
                                        steps.append((
                                            step,
                                            constraint,
                                            constraint_source.get(original_constraint, None),
                                        ))
                                        continue

                        if constraint.args[1].op == "BVS":      # arm32
                            # access constraint.args[1].args[2]
                            if constraint.args[1].args[2] is delta or constraint.args[1] is delta:
                                if constraint.args[0].op == 'BVV':
                                    step = constraint.args[0].args[0]
                                    if step != 0:
                                        steps.append((
                                            step,
                                            constraint,
                                            constraint_source.get(original_constraint, None),
                                        ))
                                        continue
        return steps

    def _discover_temp_deltas(self, state: 'SimState') -> List[Tuple[int,claripy.ast.Base,Tuple[int,int]]]:
        """
        Discover all possible temperature that may be required to transition the current state to successor states.

        :param state:   The current initial state.
        :return:        A list of ints where each int represents the required interval in number of seconds.
        """
        if self._temp_addr is None:
            return []
        state = self._initialize_state(state)
        temp_deltas = self._symbolically_advance_temp(state)
        # setup inspection points to catch where comparison happens
        constraint_source = { }
        constraint_logger = ConstraintLogger(constraint_source)
        bp_0 = BP(when=BP_BEFORE, enabled=True, action=constraint_logger.on_adding_constraints)
        state.inspect.add_breakpoint('constraints', bp_0)

        next_state = self._traverse_one(state)

        # detect required temp delta
        steps: List[Tuple[int,claripy.ast.Base,Tuple[int,int]]] = [ ]
        if temp_deltas:
            for delta in temp_deltas:
                for constraint in next_state.solver.constraints:
                    original_constraint = constraint

                    if constraint.op == "__eq__" and constraint.args[0] is delta:
                        continue
                    elif constraint.op == 'Not':
                        if len(constraint.args[0].args[1].args) > 2:
                            if constraint.args[0].args[1].args[2] is delta:
                                if constraint.args[0].args[0].op == 'FPV':
                                    step = constraint.args[0].args[0]._model_concrete.value
                                    if step != 0 and step < 10000:
                                        steps.append((
                                            step,
                                            constraint,
                                            constraint_source.get(original_constraint, None),
                                        ))
                                        continue
                        elif len(constraint.args[0].args[0].args) > 2:
                            if constraint.args[0].args[0].args[2] is delta:
                                if constraint.args[0].args[1].op == 'FPV':
                                    step = constraint.args[0].args[1]._model_concrete.value
                                    if step != 0 and step < 10000:
                                        steps.append((
                                            step,
                                            constraint,
                                            constraint_source.get(original_constraint, None),
                                        ))
                                        continue

        return steps

    def _discover_rollsensor_deltas(self, state: 'SimState') -> List[Deltas]:
        """
        Discover all possible roll sensor that may be required to transition the current state to successor states.

        :param state:   The current initial state.
        :return:        A list of ints where each int represents the required interval in number of seconds.
        """
        if self._rollsensor_addr is None:
            return []
        # import ipdb; ipdb.set_trace()
        state = self._initialize_state(state)
        prev = state.memory.load(self._rollsensor_addr, size=4, endness=self.project.arch.memory_endness)
        prev_rollsensor = state.solver.eval(prev)
        curr_id = state.solver.eval(state.memory.load(self.state_id_addr, 1))
        rollsensor_deltas = self._symbolically_advance_rollsensor(state)
        # setup inspection points to catch where comparison happens
        constraint_source = {}
        constraint_logger = ConstraintLogger(constraint_source)
        bp_0 = BP(when=BP_BEFORE, enabled=True, action=constraint_logger.on_adding_constraints)
        state.inspect.add_breakpoint('constraints', bp_0)

        next_states = self._traverse_one(state, discover=True)
        # import ipdb; ipdb.set_trace()
        # next_state = next_states[0]
        # detect required rollsensor delta
        steps: List[Deltas] = []
        deltas_info = []

        # ------------------------------------------------------------
        if rollsensor_deltas:
            for next_state in next_states:
                next_id = next_state.solver.eval(next_state.memory.load(self.state_id_addr,1))
                delta_info = {'curr_id': curr_id, 'next_id': next_id, 'state': next_state, 'step_info': [], 'same_range': False}

                for delta in rollsensor_deltas:     # Question: in which case it will return multiple deltas?
                    delta_info['delta'] = delta
                    if next_state.solver.satisfiable(extra_constraints=(delta == prev_rollsensor,)):
                        # import ipdb; ipdb.set_trace()
                        delta_info['same_range'] = True
                        # fixme: should we remove this part since we are checking state id
                        # continue
                        pass


                    for constraint in next_state.solver.constraints:
                        original_constraint = constraint

                        if delta.args[0] in constraint.variables:
                            print(constraint)
                            # add logic to simplify -1*var
                            # import ipdb; ipdb.set_trace()
                            op = constraint.op

                            if constraint.args[0].op == '__mul__' and constraint.args[0].args[1] is delta   \
                                    and constraint.args[0].args[0].op == 'BVV'  \
                                    and constraint.args[0].args[0] is claripy.BVV(-1, constraint.args[0].args[0].args[1]):
                                if op == 'SLE':  # Question: can this be generalized?
                                    left = constraint.args[0].args[1]
                                    right = constraint.args[1] * -1
                                    simplified_constraint = claripy.ops.SGE(left, right)
                                    constraint = simplified_constraint
                                    # import ipdb; ipdb.set_trace()
                                elif op == 'SGE':
                                    left = constraint.args[0].args[1]
                                    right = constraint.args[1] * -1
                                    simplified_constraint = claripy.ops.SLE(left, right)
                                    constraint = simplified_constraint
                                    # import ipdb; ipdb.set_trace()
                                elif op == 'SLT':
                                    left = constraint.args[0].args[1]
                                    right = constraint.args[1] * -1
                                    simplified_constraint = claripy.ops.SGT(left, right)
                                    constraint = simplified_constraint
                                    # import ipdb; ipdb.set_trace()
                                elif op == 'SGT':
                                    left = constraint.args[0].args[1]
                                    right = constraint.args[1] * -1
                                    simplified_constraint = claripy.ops.SLT(left, right)
                                    constraint = simplified_constraint
                                    # import ipdb; ipdb.set_trace()
                                else:
                                    import ipdb; ipdb.set_trace()
                            '''
                            if constraint.args[0].op == '__add__':

                                arg_num = len(constraint.args[0].args)
                                if arg_num != 2:
                                    import ipdb; ipdb.set_trace()

                                # TODO: generalize it when -1 is in different position
                                if constraint.args[0].args[0].op == '__mul__' and constraint.args[0].args[1].op == '__mul__' \
                                        and constraint.args[0].args[0].args[0].op == 'BVV' \
                                        and constraint.args[0].args[0].args[0] is claripy.BVV(-1, constraint.args[0].args[0].args[0].args[1]) \
                                        and constraint.args[0].args[1].args[0].op == 'BVV' \
                                        and constraint.args[0].args[1].args[0] is claripy.BVV(-1, constraint.args[0].args[0].args[0].args[1]):
                                    if op == 'SLE':     # Question: can this be generalized?
                                        left = constraint.args[0].args[0].args[1] + constraint.args[0].args[1].args[1]
                                        right = constraint.args[1] * -1
                                        simplified_constraint = claripy.ops.SGE(left, right)
                                        constraint = simplified_constraint
                                        # import ipdb; ipdb.set_trace()
                                    elif op == 'SGE':
                                        left = constraint.args[0].args[0].args[1] + constraint.args[0].args[1].args[1]
                                        right = constraint.args[1] * -1
                                        simplified_constraint = claripy.ops.SLE(left, right)
                                        constraint = simplified_constraint
                                        # import ipdb; ipdb.set_trace()
                                    elif op == 'SLT':
                                        left = constraint.args[0].args[0].args[1] + constraint.args[0].args[1].args[1]
                                        right = constraint.args[1] * -1
                                        simplified_constraint = claripy.ops.SGT(left, right)
                                        constraint = simplified_constraint
                                        # import ipdb; ipdb.set_trace()
                                    elif op == 'SGT':
                                        left = constraint.args[0].args[0].args[1] + constraint.args[0].args[1].args[1]
                                        right = constraint.args[1] * -1
                                        simplified_constraint = claripy.ops.SLT(left, right)
                                        constraint = simplified_constraint
                                        # import ipdb; ipdb.set_trace()
                                    else:
                                        import ipdb; ipdb.set_trace()
                            '''

                        else:
                            # pass if delta is not in this constraint
                            continue

                        if constraint.op == "__eq__" and constraint.args[0] is delta:
                            continue

                        elif constraint.op in ['SLE', 'SLT', 'SGT', 'SGE']:
                            if constraint.args[0] is delta:      # fixme
                                if constraint.args[1].op == 'BVV':
                                    step = constraint.args[1]._model_concrete.value
                                    step_info = (
                                        step,
                                        constraint,
                                        constraint_source.get(original_constraint, None),
                                        )

                                    delta_info['step_info'].append(step_info)
                                    continue

                        elif constraint.op == 'Or' and delta.args[0] in constraint.variables:     # wierd constraint, fixme
                            # in Recovery
                            # import ipdb; ipdb.set_trace()
                            blank = self.project.factory.blank_state()
                            blank.solver.add(constraint)
                            step = blank.solver.min(delta)
                            print(step)
                            step_info = (
                                step,
                                constraint,
                                constraint_source.get(original_constraint, None),
                            )

                            delta_info['step_info'].append(step_info)
                            continue

                deltas_info.append(delta_info)
            # import ipdb; ipdb.set_trace()

            # TODO: put this part in a function
            for each_delta_info in deltas_info:
                # fixme here adding checks for other output variables
                if each_delta_info['curr_id'] == each_delta_info['next_id']:
                    # fixme here if we want to track constraints for self loops
                    # import ipdb; ipdb.set_trace()
                    continue
                else:
                # if each_delta_info['step_info']:
                    # add object to list
                    for i in range(len(steps)):
                        if steps[i].next_id == each_delta_info['next_id']:
                            one_step = steps[i]
                    else:
                        one_step = self.Deltas(curr_id=each_delta_info['curr_id'], next_id=each_delta_info['next_id'],
                                               state=each_delta_info['state'], delta=each_delta_info['delta'])
                        i = len(steps)
                        steps.append(one_step)

                    # parse info and update object
                    all_step_info = each_delta_info['step_info']
                    new_constraint = None
                    for one_step_info in all_step_info:
                        # create new constraint
                        if new_constraint is not None:
                            # logic AND all constraints in one state
                            new_constraint = claripy.And(new_constraint, one_step_info[1])
                        else:
                            new_constraint = one_step_info[1]

                        if one_step_info[0] not in one_step.steps:
                            one_step.steps.append(one_step_info[0])
                        if one_step_info[2] not in one_step.constraint_sources:
                            one_step.constraint_sources.append(one_step_info[2])

                    if one_step.constraint:
                        # logic OR all constraints in different states
                        one_step.constraint = claripy.Or(new_constraint, one_step.constraint)
                    else:
                        one_step.constraint = new_constraint
                    steps[i] = one_step

            for each in steps:
                # import ipdb; ipdb.set_trace()
                blank_state = self.project.factory.blank_state()
                blank_state.solver.add(each.constraint)
                # add delta range (-18000, 18000)
                blank_state.solver.add(claripy.SLT(delta, 18000))
                blank_state.solver.add(claripy.SGT(delta, -18000))
                each.new_value = blank_state.solver.min(each.delta, signed=True) + 1     # fixme: min or max or eval?
                # if blank_state.solver.eval(claripy.SLE(claripy.BVV(each.new_value,32), claripy.BVV(-18000,32))):
                #     import ipdb; ipdb.set_trace()

            # -----------------------------------

            # if len(steps) == 0 and len(next_states) == 2:
            #     # found branches but not deltas
            #     import ipdb; ipdb.set_trace()
            #     for each_delta_info in deltas_info:
            #         if not each_delta_info['same_range']:
            #             one_step = self.Deltas(curr_id=each_delta_info['curr_id'], next_id=each_delta_info['next_id'],
            #                                    state=each_delta_info['state'], delta=each_delta_info['delta'])
            #
            #             one_step.steps.append(each_delta_info['step_info'][0][0])
            #             one_step.constraint = each_delta_info['step_info'][0][1]
            #             one_step.constraint_sources.append(each_delta_info['step_info'][0][2])
            #             one_step.new_value = each_delta_info['step_info'][0][0]
            #             steps.append(one_step)


        # TODO: return original step_info
        return steps

    def _simplify_constraint(self, constraint: claripy.ast.Base, source: Dict[claripy.ast.Base,Any]) -> Tuple[Optional[claripy.ast.Base],Dict[claripy.ast.Base,Any]]:
        """
        Attempt to simplify a constraint and generate a new source mapping.

        Note that this simplification focuses on readability and is not always sound!

        :param constraint:
        :param source:
        :return:
        """

        if (constraint.op in ("__ne__", "__eq__", "ULE")
                and constraint.args[0].op == "__add__"
                and constraint.args[1].op == "__add__"):
            # remove arguments that appear in both sides of the comparison
            same_args = set(constraint.args[0].args).intersection(set(constraint.args[1].args))
            if same_args:
                left_new_args = tuple(arg for arg in constraint.args[0].args if arg not in same_args)
                left = constraint.args[0].make_like("__add__", left_new_args) if len(left_new_args) > 1 else left_new_args[0]
                if constraint.args[0] in source:
                    source[left] = source[constraint.args[0]]

                right_new_args = tuple(arg for arg in constraint.args[1].args if arg not in same_args)
                right = constraint.args[1].make_like("__add__", right_new_args) if len(right_new_args) > 1 else right_new_args[0]
                if constraint.args[1] in source:
                    source[right] = source[constraint.args[1]]

                simplified = constraint.make_like(constraint.op, (left, right))
                if constraint in source:
                    source[simplified] = source[constraint]
                return self._simplify_constraint(simplified, source)

        # Transform signed-extension of fpToSBV() to unsigned extension
        if constraint.op == "Concat":
            args = constraint.args
            if all(arg.op == "Extract" for arg in args):
                if len(set(arg.args[2] for arg in args)) == 1:
                    if all(arg.args[0:2] in ((15,15), (31,31)) for arg in args[:-1]):
                        # found it!
                        core, source = self._simplify_constraint(args[0].args[2], source)
                        if core is None:
                            core = args[0].args[2]
                        simplified = claripy.ZeroExt(len(args) - 1, core)
                        if constraint in source:
                            source[simplified] = source[constraint]
                        return simplified, source
            elif all(arg.op == "Extract" for arg in args[:-1]):
                if len(set(arg.args[2] for arg in args[:-1])) == 1:
                    v = args[0].args[2]
                    if v is args[-1]:
                        if all(arg.args[0:2] in ((15,15), (31,31)) for arg in args[:-1]):
                            # found it!
                            core, source = self._simplify_constraint(v, source)
                            if core is None:
                                core = v
                            simplified = claripy.ZeroExt(len(args) - 1, core)
                            if constraint is source:
                                source[simplified] = source[constraint]
                            return simplified, source

        elif constraint.op in ('__ne__', '__mod__', '__floordiv__'):
            left, source = self._simplify_constraint(constraint.args[0], source)
            right, source = self._simplify_constraint(constraint.args[1], source)
            if left is None and right is None:
                return None, source
            if left is None:
                left = constraint.args[0]
            if right is None:
                right = constraint.args[1]
            simplified = constraint.make_like(constraint.op, (left, right))
            if constraint in source:
                source[simplified] = source[constraint]
            return simplified, source

        elif constraint.op in ('__add__', ):
            new_args = [ ]
            simplified = False
            for arg in constraint.args:
                new_arg, source = self._simplify_constraint(arg, source)
                if new_arg is not None:
                    new_args.append(new_arg)
                    simplified = True
                else:
                    new_args.append(arg)
            if not simplified:
                return None, source
            simplified = constraint.make_like(constraint.op, tuple(new_args))
            if constraint in source:
                source[simplified] = source[constraint]
            return simplified, source

        elif constraint.op in ('fpToSBV', 'fpToFP'):
            arg1, source = self._simplify_constraint(constraint.args[1], source)
            if arg1 is None:
                return None, source
            simplified = constraint.make_like(constraint.op, (constraint.args[0], arg1, constraint.args[2]))
            if constraint in source:
                source[simplified] = source[constraint]
            return simplified, source

        elif constraint.op in ('fpMul', ):
            if constraint.args[1].op == "FPV" and constraint.args[1]._model_concrete.value == 0.0:
                return constraint.args[1], source
            elif constraint.args[2].op == "FPV" and constraint.args[2]._model_concrete.value == 0.0:
                return constraint.args[2], source
            arg1, source = self._simplify_constraint(constraint.args[1], source)
            arg2, source = self._simplify_constraint(constraint.args[2], source)
            if arg1 is None and arg2 is None:
                return None, source
            if arg1 is None:
                arg1 = constraint.args[1]
            if arg2 is None:
                arg2 = constraint.args[2]
            simplified = constraint.make_like(constraint.op, (constraint.args[0], arg1, arg2))
            if constraint in source:
                source[simplified] = source[constraint]
            return simplified, source

        return None, source

    def _symbolize_input_fields(self, state: 'SimState') -> Dict[str,claripy.ast.Base]:

        symbolic_input_vars = { }

        for name, (address, type_, size) in self.fields.fields.items():
            # print(f"[.] Symbolizing field {name}...")

            v = state.memory.load(address, size=size, endness=self.project.arch.memory_endness)
            if not state.solver.symbolic(v):
                # if type_ == "float":
                #     concrete_v = state.solver.eval(v, cast_to=float)
                #     symbolic_v = claripy.FPS(name, claripy.fp.FSORT_FLOAT)
                # elif type_ == "double":
                #     concrete_v = state.solver.eval(v, cast_to=float)
                #     symbolic_v = claripy.FPS(name, claripy.fp.FSORT_DOUBLE)
                # else:
                concrete_v = state.solver.eval(v)
                # if name in {"channel_roll", "channel_pitch"}:
                #     # write positive numbers
                #     symbolic_v = claripy.Concat(claripy.BVV(0, 1),
                #                                 claripy.BVS(name, size * self.project.arch.byte_width - 1))
                # else:
                symbolic_v = claripy.BVS(name, size * self.project.arch.byte_width)
                symbolic_input_vars[name] = symbolic_v

                # update the value in memory
                state.memory.store(address, symbolic_v, endness=self.project.arch.memory_endness)

                # preconstrain it
                state.preconstrainer.preconstrain(concrete_v, symbolic_v)
            else:
                symbolic_input_vars[name] = v

        return symbolic_input_vars

    def _symbolize_timecounter(self, state: 'SimState') -> Dict[str,claripy.ast.Base]:
        tv_sec_addr = self._time_addr
        prev = state.memory.load(self._time_addr, size=4, endness=self.project.arch.memory_endness)
        prev_time = state.solver.eval(prev) + 1

        self._tv_sec_var = claripy.BVS('tv_sec', 4 * self.project.arch.byte_width)
        state.memory.store(tv_sec_addr, self._tv_sec_var, endness=self.project.arch.memory_endness)
        state.preconstrainer.preconstrain(
            claripy.BVV(prev_time, 4 * self.project.arch.byte_width), self._tv_sec_var)

        return {'tv_sec': self._tv_sec_var}



        # if self.software == "beremiz":
        #     return self._symbolize_timecounter_beremiz(state)
        # elif self.software == 'arduino':
        #     return self._symbolize_timecounter_arduino(state)

    # Traffic_Light Beremiz
    def _symbolize_timecounter_beremiz(self, state: 'SimState') -> Dict[str,claripy.ast.Base]:
        tv_sec_addr = self._time_addr
        tv_nsec_addr = tv_sec_addr + self.project.arch.bytes

        self._tv_sec_var = claripy.BVS('tv_sec', self.project.arch.bytes * self.project.arch.byte_width)
        self._tv_nsec_var = claripy.BVS('tv_nsec', self.project.arch.bytes * self.project.arch.byte_width)

        state.memory.store(tv_sec_addr, self._tv_sec_var, endness=self.project.arch.memory_endness)
        state.memory.store(tv_nsec_addr, self._tv_nsec_var, endness=self.project.arch.memory_endness)

        # the initial timer values are 0
        state.preconstrainer.preconstrain(claripy.BVV(0, self.project.arch.bytes * self.project.arch.byte_width), self._tv_sec_var)
        state.preconstrainer.preconstrain(claripy.BVV(0, self.project.arch.bytes * self.project.arch.byte_width), self._tv_nsec_var)

        return {
            'tv_sec_var': self._tv_sec_var,
            'tv_nsec_var': self._tv_nsec_var
        }

    # reflowoven Arduino
    def _symbolize_timecounter_arduino(self, state: 'SimState') -> Dict[str, claripy.ast.Base]:
        tv_sec_addr = self._time_addr
        prev = state.memory.load(self._time_addr, size=self.project.arch.bytes, endness=self.project.arch.memory_endness)
        prev_time = state.solver.eval(prev) + 1

        self._tv_sec_var = claripy.BVS('tv_sec', self.project.arch.bytes * self.project.arch.byte_width)
        state.memory.store(tv_sec_addr, self._tv_sec_var, endness=self.project.arch.memory_endness)
        state.preconstrainer.preconstrain(claripy.BVV(prev_time, self.project.arch.bytes * self.project.arch.byte_width), self._tv_sec_var)

        return {'tv_sec': self._tv_sec_var}

    def _symbolically_advance_timecounter(self, state: 'SimState') -> List[claripy.ast.Bits]:
        sec_delta = claripy.BVS("sec_delta", 4 * self.project.arch.byte_width)
        state.preconstrainer.preconstrain(claripy.BVV(1, 4 * self.project.arch.byte_width), sec_delta)

        tv_sec = state.memory.load(self._time_addr, size=4, endness=self.project.arch.memory_endness)
        state.memory.store(self._time_addr, tv_sec + sec_delta, endness=self.project.arch.memory_endness)

        return [sec_delta]

    def _advance_timecounter(self, state: 'SimState', delta: int) -> None:
        prev = state.memory.load(self._time_addr, size=4, endness=self.project.arch.memory_endness)
        state.memory.store(self._time_addr, prev + delta, endness=self.project.arch.memory_endness)

        if self.software == 'beremiz':
            tv_nsec = state.memory.load(self._time_addr + self.project.arch.bytes, size=self.project.arch.bytes,
                                        endness=self.project.arch.memory_endness)
            state.memory.store(self._time_addr + self.project.arch.bytes, tv_nsec + 200,
                               endness=self.project.arch.memory_endness)

    def _symbolize_rollsensor(self, state: 'SimState') -> Dict[str, claripy.ast.Base]:
        rollsensor_addr = self._rollsensor_addr

        prev = state.memory.load(self._rollsensor_addr, size=4, endness=self.project.arch.memory_endness)
        prev_rollsensor = state.solver.eval(prev)

        self._rollsensor = claripy.BVS('rollsensor', 4*self.project.arch.byte_width)
        state.memory.store(rollsensor_addr, self._rollsensor, endness=self.project.arch.memory_endness)
        state.preconstrainer.preconstrain(claripy.BVV(prev_rollsensor, 4*self.project.arch.byte_width), self._rollsensor)

        return {'rollsensor': self._rollsensor}

    def _symbolically_advance_rollsensor(self, state: 'SimState') -> List[claripy.ast.Bits]:
        rollsensor_delta = claripy.BVS("rollsensor_delta", 4*self.project.arch.byte_width)
        # state.preconstrainer.preconstrain(claripy.BVV(1, 4*self.project.arch.byte_width), rollsensor_delta)
        # roll sensor range is (-180, 180)
        # state.add_constraints(claripy.ops.SGT(rollsensor_delta, -18000), claripy.ops.SLT(rollsensor_delta, 18000))

        # prev = state.memory.load(self._rollsensor_addr, size=4, endness=self.project.arch.memory_endness)
        # state.memory.store(self._rollsensor_addr, prev + rollsensor_delta, endness=self.project.arch.memory_endness)
        state.memory.store(self._rollsensor_addr, rollsensor_delta, endness=self.project.arch.memory_endness)
        return [rollsensor_delta]

    def _symbolically_advance_rollsensor_concolic(self, state: 'SimState') -> List[claripy.ast.Bits]:
        rollsensor_delta = claripy.BVS("rollsensor_delta", 4*self.project.arch.byte_width)
        state.preconstrainer.preconstrain(claripy.BVV(1, 4*self.project.arch.byte_width), rollsensor_delta)
        # roll sensor range is (-180, 180)
        # state.add_constraints(claripy.ops.SGT(rollsensor_delta, -18000), claripy.ops.SLT(rollsensor_delta, 18000))

        prev = state.memory.load(self._rollsensor_addr, size=4, endness=self.project.arch.memory_endness)
        state.memory.store(self._rollsensor_addr, prev + rollsensor_delta, endness=self.project.arch.memory_endness)
        # state.memory.store(self._rollsensor_addr, rollsensor_delta, endness=self.project.arch.memory_endness)
        return [rollsensor_delta]

    def _advance_rollsensor(self, state: 'SimState', delta) -> None:
        self._rollsensor = claripy.BVS('rollsensor', 4*self.project.arch.byte_width)
        state.memory.store(self._rollsensor_addr, self._rollsensor, endness=self.project.arch.memory_endness)
        state.preconstrainer.preconstrain(claripy.BVV(delta, 4*self.project.arch.byte_width), self._rollsensor)

    def _symbolize_temp(self, state: 'SimState') -> Dict[str, claripy.ast.Base]:
        temp_addr = self._temp_addr

        prev = state.memory.load(self._temp_addr, size=8, endness=self.project.arch.memory_endness)
        prev_temp = state.solver.eval(prev)

        self._temperature = claripy.FPS('temperature', claripy.fp.FSORT_DOUBLE)
        state.memory.store(temp_addr, self._temperature, endness=self.project.arch.memory_endness)
        state.preconstrainer.preconstrain(state.solver.BVV(prev_temp, 64).raw_to_fp(), self._temperature)

        return {'temperature': self._temperature}

    def _symbolically_advance_temp(self, state: 'SimState') -> List[claripy.ast.Bits]:
        temp_delta = claripy.FPS("temp_delta", claripy.fp.FSORT_DOUBLE)
        state.preconstrainer.preconstrain(state.solver.FPV(0.5, claripy.fp.FSORT_DOUBLE), temp_delta)

        prev = state.memory.load(self._temp_addr, size=8, endness=self.project.arch.memory_endness).raw_to_fp()
        state.memory.store(self._temp_addr, prev + temp_delta, endness=self.project.arch.memory_endness)

        return [temp_delta]

    def _advance_temp(self, state: 'SimState', delta) -> None:
        self._temperature = claripy.FPS('temperature', claripy.fp.FSORT_DOUBLE)
        state.memory.store(self._temp_addr, self._temperature, endness=self.project.arch.memory_endness)
        state.preconstrainer.preconstrain(claripy.FPV(delta, claripy.fp.FSORT_DOUBLE), self._temperature)

    def _traverse_one(self, state: 'SimState', unsat_flag: bool = False, discover: bool = False):

        simgr = self.project.factory.simgr(state, save_unsat=unsat_flag)

        while simgr.active:
            s = simgr.active[0]
            # print(simgr.active)
            # print(s.memory.load(self._time_addr, 4, endness=self.project.arch.memory_endness))
            # print(s.solver.constraints[-10:])

            if not discover:    # ignore multiple states when discovering deltas
                if len(simgr.active) > 1:
                    import ipdb; ipdb.set_trace()

            # if unsat_flag:
            #     if simgr.unsat:
            #         print("unsat")
            #         import ipdb; ipdb.set_trace()
            #
            # if s.addr == 0x47e45e:
            #     print("check flip angle in roll")
            #     import ipdb; ipdb.set_trace()

            if s.addr == 0x47e336:
                print("START!")
            if s.addr == 0x47e3e4:
                print("ROLL!")
            if s.addr == 0x47e491:
                print("PITCH_A!")
            if s.addr == 0x47e558:
                print("PITCH_B!")
            if s.addr == 0x47e61f:
                print("RECOVER!")
            if s.addr == 0x47e75c:
                print("ABANDON!")
            if s.addr == 0x47e70d:
                print("finish recovery!")
                # import ipdb; ipdb.set_trace()
            # if s.addr == 0x47e312 or s.addr == 0x47e2ff:
            #     print("check time")
            #     import ipdb; ipdb.set_trace()

            # import ipdb; ipdb.set_trace()

            simgr.stash(lambda x: x.addr == self._ret_trap, from_stash='active', to_stash='finished')

            simgr.step()
        # import ipdb; ipdb.set_trace()
        # import sys
        # sys.stdout.write('\n')
        if not discover:
            assert len(simgr.finished) == 1
            return simgr.finished[0]
        else:
            return simgr.finished

    def _initialize_state(self, init_state=None) -> 'SimState':
        if init_state is not None:
            s = init_state.copy()
            s.ip = self.func.addr
            # TODO: pass object address to StateGraphRecovery as arguments
            s.regs.rdi = 0x8f9b88    # mode_flip_addr
        else:
            s = self.project.factory.blank_state(addr=self.func.addr)
            s.regs.rdi = 0xc0000000
            s.memory.store(0xc0000000, b"\x00" * 0x1000)

        # disable cross instruction optimization so that statement IDs in symbolic execution will match the ones used in
        # static analysis
        s.options[NO_CROSS_INSN_OPT] = True
        # disable warnings
        s.options[SYMBOL_FILL_UNCONSTRAINED_MEMORY] = True
        s.options[SYMBOL_FILL_UNCONSTRAINED_REGISTERS] = True
        s.options[SIMPLIFY_CONSTRAINTS] = True

        if self.project.arch.call_pushes_ret:
            s.stack_push(claripy.BVV(self._ret_trap, self.project.arch.bits))
        else:
            # set up the link register for the return address
            s.regs.lr = self._ret_trap

        return s


AnalysesHub.register_default('StateGraphRecovery', StateGraphRecoveryAnalysis)
