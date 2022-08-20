import os
import struct
from typing import TYPE_CHECKING

import networkx
import sys
import json
import claripy
import angr
from angr.sim_options import ZERO_FILL_UNCONSTRAINED_MEMORY
# from angr.analyses.state_graph_recovery import MinDelayBaseRule, RuleVerifier, IllegalNodeBaseRule
from angr.analyses.state_graph_recovery.apis import generate_patch, apply_patch, apply_patch_on_state, EditDataPatch

if TYPE_CHECKING:
    import networkx


binaries_base = os.path.join(os.path.dirname(os.path.realpath(__file__)), '..', '..', 'binaries')


class millis(angr.SimProcedure):
    def run(self):
        # import ipdb; ipdb.set_trace()
        # time_addr = 0x200001d8 # a random number
        prev = self.state.memory.load(time_addr, 4, endness=self.arch.memory_endness)
        # self.state.memory.store(time_addr, prev + usec, endness=self.arch.memory_endness)
        # print(self.state.solver.eval(self.state.memory.load(0x200002fc, 4, endness=self.arch.memory_endness)))
        self.state.regs._eax = prev
        return None


class WriteEvent(angr.SimProcedure):
    def run(self, this, logevent):
        print("[LOG EVENT] ", logevent)
        return None

#
# class sinf(angr.SimProcedure):
#     def run(self, x):
#         print("in sinf")
#         import ipdb; ipdb.set_trace()
#         return None
#
#
# class cosf(angr.SimProcedure):
#     def run(self, x):
#         print("in cosf")
#         import ipdb; ipdb.set_trace()
#         return None


class is_zero(angr.SimProcedure):
    def run(self, x):
        # print("in is_zero!")
        # import ipdb;ipdb.set_trace()
        x_num = self.state.regs._xmm0
        x_bytes = struct.pack("@P", x_num.args[0])
        x_float = struct.unpack("<d", x_bytes)[0]
        self.state.regs._al = claripy.If(x_float==0, claripy.BVV(1, 8), claripy.BVV(0, 8))
        return None


class abs(angr.SimProcedure):
    def run(self, x):
        # print("in abs!")
        # import ipdb;ipdb.set_trace()
        x_num = self.state.regs._eax
        self.state.regs._eax = claripy.If(claripy.ops.SGE(x_num, 0), x_num, -x_num)
        return None


def call_one_func(state: 'SimState') -> 'SimState':
    ret_trap = 0x1f32ff40

    if state.project.arch.call_pushes_ret:
        state.stack_push(claripy.BVV(ret_trap, state.project.arch.bits))

    simgr = state.project.factory.simgr(state)
    while simgr.active:
        # print(simgr.active)
        s = simgr.active[0]
        # if len(simgr.active) > 1:
        #     import ipdb; ipdb.set_trace()
        if s.addr == 0x458158:  # armed()
            # TODO: Should i move since i initialized motors?
            # rdi is motors object i dont know how to initialize it
            # import ipdb; ipdb.set_trace()
            s.memory.store(s.regs.rdi + 0x80, claripy.BVV(1, 8), endness = s.project.arch.memory_endness)

#        if s.addr == 0x47dfc4:
#           print("after abs")
#           import ipdb; ipdb.set_trace()

        simgr.stash(lambda x: x.addr == ret_trap, from_stash='active', to_stash='finished')
        simgr.step()

    initial_states = simgr.finished
    return initial_states

# analyse state machine in ModeFlip
def test_flip():
    binary_path = "/home/bonnie/PLCRCA/arducopter/arducopter_nobuildin"
    variable_path = ""

    proj = angr.Project(binary_path)
    cfg = proj.analyses.CFG()

    # a random number
    global time_addr
    time_addr = 0x1f34ff80

    # import ipdb; ipdb.set_trace()
    proj.hook_symbol('_ZN6AP_HAL6millisEv', millis())
    proj.hook_symbol('_ZN6AP_HAL8micros64Ev', millis())
    proj.hook_symbol('_ZN9AP_Logger11Write_EventE8LogEvent', WriteEvent())
    proj.hook_symbol('abs', abs())




    ret_trap = 0x1f32ff40
    # ret_trap1 = 0x1f32ff80

    copter_constructor_addr = 0x4604d4
    # init_rc_in_addr = 0x48c606
    # allocate_motors = 0x48f07a
    # constructor_addr = 0x472ca2     # Mode::Mode()
    mode_constructor_addr = 0x4601b2     # ModeFlip::ModeFlip()
    init_addr = 0x47df04    # ModeFlip::init()
    run_addr = 0x47e1cc    # ModeFLip::run()

    copter_addr = 0x8f1a00
    mode_flip_addr = copter_addr + 0x8188   # 0x8f9b88
    ahrs_addr = copter_addr + 0x2480
    motors_addr = copter_addr + 0x5cf0  # 0xc00042f0
    channel_roll_addr = 0x980000
    channel_pitch_addr = 0x981000


    # run the state initializer
    blank = proj.factory.blank_state(addr=copter_constructor_addr, add_options={ZERO_FILL_UNCONSTRAINED_MEMORY})
    blank.regs.rbp = 0x920000
    blank.regs.rdi = copter_addr
    blank.regs.rsi = 0x951000
    print("copter constructor")
    copter_state = call_one_func(blank)

    # initialize RC_Channel
    blank = copter_state[0].copy()
    blank.memory.store(copter_addr + 0x5500, claripy.BVV(channel_roll_addr, 64), endness=proj.arch.memory_endness)
    blank.memory.store(copter_addr + 0x5508, claripy.BVV(channel_pitch_addr, 64), endness=proj.arch.memory_endness)
    # set channel value
    blank.memory.store(channel_roll_addr + 0xc, claripy.BVS('channel_roll', 16), endness=proj.arch.memory_endness)
    blank.memory.store(channel_pitch_addr + 0xc, claripy.BVS('channel_pitch', 16), endness=proj.arch.memory_endness)
    rc_state = blank
    # import ipdb; ipdb.set_trace()

    # initialize motors
    blank = rc_state.copy()
    print("allocate_motors")
    blank.regs.rip = 0x49473b   # line 452
    # mov  [rbp+this], rdi
    blank.memory.store(blank.regs.rbp-0x38, claripy.BVV(copter_addr, 64), endness=proj.arch.memory_endness)
    simgr = proj.factory.simgr(blank)
    while simgr.active:
        # print(simgr.active)
        s = simgr.active[0]
        if s.addr == 0x494959:
            # import ipdb; ipdb.set_trace()
            break
        simgr.step()

    motor_state = simgr.active[0]

    # initialize attitude control
    blank = motor_state.copy()
    print("allocate attitude control")
    blank.regs.rip = 0x494a8d   # line 524
    simgr = proj.factory.simgr(blank)
    while simgr.active:
        # print(simgr.active)
        s = simgr.active[0]
        if s.addr == 0x494b1f:
            # import ipdb; ipdb.set_trace()
            break
        simgr.step()
    # import ipdb; ipdb.set_trace()
    att_state = simgr.active[0]

    blank = att_state.copy()
    blank.regs.rip = mode_constructor_addr
    print("mode constructor")
    mode_state = call_one_func(blank)

    blank = mode_state[0].copy()
    blank.regs.rip = init_addr
    blank.regs.rdi = mode_flip_addr
    blank.regs.rsi = 1
    print("modeflip init")
    initial_states = call_one_func(blank)       # here should be 4 states

    # proj.hook_symbol('sinf', sinf())
    # proj.hook_symbol('cosf', cosf())
    proj.hook_symbol('_Z7is_zerof', is_zero())

    # make sure init function returns true
    for s in initial_states:
        if s.solver.eval(s.regs.eax) == 0:
            continue
        else:

            # import ipdb; ipdb.set_trace()
            initial_state = s
            # TODO: this should be output variables, we should add an input variable dict
            # what are output variables in this case? `throttle_out` is a local variable
            fields_desc = {
                'state': (mode_flip_addr + 0x84, "byte", 1),
                # 'channel_roll': (channel_roll_addr + 0xc, "int", 2),
                # 'channel_pitch': (channel_pitch_addr + 0xc, "int", 2),
                # 'roll_dir': (mode_flip_addr + 0x8c, "byte", 1),        #  0x8f9c14
                # 'pitch_dir': (mode_flip_addr + 0x8d, "byte", 1),
                'roll_sensor': (ahrs_addr + 0x394, "int", 4)
            }

            fields = angr.analyses.state_graph_recovery.AbstractStateFields(fields_desc)
            func = cfg.kb.functions['_ZN8ModeFlip3runEv']
            initial_state.regs.rdi = mode_flip_addr     # TODO: pass object address to StateGraphRecovery as arguments
            sgr = proj.analyses.StateGraphRecovery(func, fields, "arduino", time_addr, rollsensor_addr = ahrs_addr + 0x394, init_state=initial_state)

            # output the graph to a dot file
            from networkx.drawing.nx_agraph import write_dot
            write_dot(sgr.state_graph, "roll.dot")

           # import ipdb; ipdb.set_trace()


if __name__ == "__main__":
    test_flip()
