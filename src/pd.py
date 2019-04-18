"""
This file contains code for the Primal Dual research project
"""

from __future__ import annotations

from itertools import product, chain, combinations

from syntax import *
from mypyvy import *

# form: https://docs.python.org/3/library/itertools.html#itertools-recipes
def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))


def reachability_tree(s: Solver, prog: Program) -> None:
    print('hey oded and kartik')

    models: List[Model] = []

    # somehow, we got this list of formulas
    l: List[Expr]

    inits = [init.expr for init in prog.inits()]
    res = check_two_state_implication_all_transitions(s, prog, inits, l[0])
    if res is not None:
        z3m, ition = res
        models.append(Model(prog, z3m, s, [KEY_NEW, KEY_OLD]))

    for e in l[1:]:
        res = check_two_state_implication_all_transitions(s, prog, [models[-1].as_onestate_formula(i=0)], e)
        if res is not None:
            z3m, ition = res
            models.append(Model(prog, z3m, s, [KEY_NEW, KEY_OLD]))

State = Model

def alpha(s:Solver, states: List[State] , top_clause:Expr) -> List[Expr]:
    assert isinstance(top_clause, QuantifierExpr)
    assert isinstance(top_clause.body, NaryExpr)
    assert top_clause.body.op == 'OR'
    assert set(top_clause.body.free_ids()) == set(v.name for v in top_clause.binder.vs)
    literals = top_clause.body.args
    assert len(set(literals)) == len(literals)

    result = []
    for lits in powerset(literals):
        vs = [v for v in top_clause.binder.vs
             if v.name in set(n for lit in lits for n in lit.free_ids())]
        if len(vs) > 0:
            clause = Forall(vs, Or(*lits))
        else:
            clause = Or(*lits)
        #if all(is_true(m.z3model.eval(s.get_translator(m.keys[0]).translate_expr(clause))) for m in states):
        #    result.append(clause)
    return result

def forward_explore(s: Solver, prog: Program, alpha: Callable[[List[Model]], List[Expr]]) -> None:

    states: List[State] = []
    a: List[Expr] = alpha([])

    changes = True
    while changes:
        changes = False

        # check for initial states violating a
        z3m = check_implication(s, prog.inits(), a)
        if z3m is not None:
            states.append(Model(prog, z3m, s, [KEY_ONE]))
            changes = True
            a = alpha(states)
            continue

        # check for 1 transition from an initial state or a state in states
        for prestate, p in product([None] + states, a):
            if prestate is None:
                precondition = prog.inits()
            else:
                precondition = [prestate.as_onestate_formula(i=0)]
            res = check_two_state_implication_all_transitions(s, prog, precondition, p)
            if res is not None:
                z3m, ition = res
                states.append(Model(prog, z3m, s, [KEY_NEW, KEY_OLD]))
                changes = True
                a = alpha(states)
                break

    # here init U states |= a, post(init U states) |= a

    print(states)
    print(a)



def pd_add_argparsers(subparsers: argparse._SubParsersAction) -> List[argparse.ArgumentParser]:
    reachability_tree_subparser = subparsers.add_parser('reachability-tree', help='TODO write help')
    reachability_tree_subparser.set_defaults(main=reachability_tree)
    return [reachability_tree_subparser]
