
from ..virtual_dispatcher import resolve_method
from .base import SimSootExpr


class SimSootExpr_VirtualInvoke(SimSootExpr):
    def __init__(self, expr, state):
        super(SimSootExpr_VirtualInvoke, self).__init__(expr, state)

    def _execute(self):
        invoke_target = resolve_method(self.state, self.expr)

        # Initialize an invoke state, and set the arguments
        self.state.scratch.invoke = True
        self.state.scratch.invoke_target = invoke_target
        self.state.scratch.invoke_expr = self.expr
        self.state.scratch.invoke_has_native_target = ('NATIVE' in invoke_target.attrs)