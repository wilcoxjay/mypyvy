import syntax
import logic
from logic import Solver, Expr
import utils
import z3

from typing import Callable, List, Optional

def translate_transition_call(s: Solver, key: str, key_old: str, c: syntax.TransitionCall) -> z3.ExprRef:
    prog = syntax.the_program
    ition = prog.scope.get_definition(c.target)
    assert ition is not None
    lator = s.get_translator(key, key_old)
    bs = lator.bind(ition.binder)
    qs: List[Optional[z3.ExprRef]] = [b for b in bs]
    if c.args is not None:
        for j, a in enumerate(c.args):
            if isinstance(a, Expr):
                bs[j] = lator.translate_expr(a)
                qs[j] = None
            else:
                assert isinstance(a, syntax.Star)
    qs1 = [q for q in qs if q is not None]
    with lator.scope.in_scope(ition.binder, bs):
        body = lator.translate_transition_body(ition)
    if len(qs1) > 0:
        return z3.Exists(qs1, body)
    else:
        return body


def bmc_trace(prog: syntax.Program, trace: syntax.TraceDecl,
              s: Solver, sat_checker: Callable[[Solver, List[str]], Optional[logic.Trace]],
              log: bool=False
) -> Optional[logic.Trace]:
    n_states = len(list(trace.transitions())) + 1
    if log:
        print('%s states' % (n_states,))

    keys = ['state%02d' % i for i in range(n_states)]

    for k in keys:
        s.get_translator(k)  # initialize all the keys before pushing a solver stack frame

    with s:
        lator = s.get_translator(keys[0])
        if len(trace.components) > 0 and not isinstance(trace.components[0], syntax.AssertDecl):
            for init in prog.inits():
                s.add(lator.translate_expr(init.expr))

        i = 0
        for c in trace.components:
            if isinstance(c, syntax.AssertDecl):
                if c.expr is None:
                    if i != 0:
                        utils.print_error_and_exit(c.tok, 'assert init is only allowed in the first state')
                    for init in prog.inits():
                        s.add(s.get_translator(keys[i]).translate_expr(init.expr))
                else:
                    s.add(s.get_translator(keys[i]).translate_expr(c.expr))
            else:
                te: syntax.TransitionExpr = c.transition
                if isinstance(te, syntax.AnyTransition):
                    logic.assert_any_transition(s, str(i), keys[i + 1], keys[i], allow_stutter=True)
                else:
                    l = []
                    for call in te.calls:
                        tid = z3.Bool(logic.get_transition_indicator(str(i), call.target))
                        l.append(tid)
                        s.add(tid == translate_transition_call(s, keys[i + 1], keys[i], call))
                    s.add(z3.Or(*l))

                i += 1

        return sat_checker(s, keys)
