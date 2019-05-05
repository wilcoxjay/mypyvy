'''
This file contains code for the Primal Dual research project
'''

from __future__ import annotations

from itertools import product, chain, combinations

from syntax import *
from mypyvy import *

from typing import TypeVar, Iterable

A = TypeVar('A')
# form: https://docs.python.org/3/library/itertools.html#itertools-recipes
def powerset(iterable: Iterable[A]) -> Iterator[Tuple[A, ...]]:
    'powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)'
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))


State = Model


def alpha_from_clause(s:Solver, states: List[State] , top_clause:Expr) -> List[Expr]:
    assert isinstance(top_clause, QuantifierExpr)
    assert isinstance(top_clause.body, NaryExpr)
    assert top_clause.body.op == 'OR'
    #assert set(top_clause.body.free_ids()) == set(v.name for v in top_clause.binder.vs)
    literals = top_clause.body.args
    assert len(set(literals)) == len(literals)

    result: List[Expr] = []
    for lits in powerset(literals):
        vs = [v for v in top_clause.binder.vs
             if v.name in set(n for lit in lits for n in lit.free_ids())]
        if len(vs) > 0:
            clause : Expr = Forall(vs, Or(*lits))
        else:
            clause = Or(*lits)
        if all(check_implication(s, [m.as_onestate_formula(0)], [clause]) is None for m in states):
            # z3.is_true(m.z3model.eval(s.get_translator(m.keys[0]).translate_expr(clause))) for m in states):
            result.append(clause)
    return result


def forward_explore(s: Solver, prog: Program, alpha: Callable[[List[Model]], List[Expr]]) -> Tuple[List[State], List[Expr]]:

    states: List[State] = []
    a = alpha([])
    inits = [init.expr for init in prog.inits()]

    changes = True
    while changes:
        changes = False

        # check for initial states violating a
        z3m = check_implication(s, inits, a)
        if z3m is not None:
            states.append(Model(prog, z3m, s, [KEY_ONE]))
            changes = True
            a = alpha(states)
            continue

        # check for 1 transition from an initial state or a state in states
        for prestate, p in product(itertools.chain([None], states), a):
            # print('Checking if {} satisfies WP of {}'.format(prestate is None, p))
            if prestate is None:
                precondition = inits
            else:
                precondition = [prestate.as_onestate_formula(0)]
            res = check_two_state_implication_all_transitions(s, prog, precondition, p)
            # print(res)
            if res is not None:
                z3m, ition = res
                states.append(Model(prog, z3m, s, [KEY_NEW, KEY_OLD]))
                changes = True
                a = alpha(states)
                break

    # here init U states |= a, post(init U states) |= a
    # here init U states |= a /\ wp(a)

    #print(states)
    #print(a)
    return states, a


def forward_explore_inv(s: Solver, prog: Program) -> None:
    invs = [inv.expr for inv in prog.invs()]
    print('Performing forward explore w.r.t. the following clauses:')
    for p in sorted(invs, key=lambda x: len(str(x))):
        print(p)
    print('='*80)
    alpha  = lambda states: list(set(chain(*(alpha_from_clause(s, states, inv) for inv in invs))))
    states, a = forward_explore(s, prog, alpha)
    len(states)
    print('Done!\n' + '='*80)
    print('The resulting invariant after forward exporation:')
    for p in sorted(a, key=lambda x: len(str(x))):
        print(p)
    print('='*80)
    print(f'Found {len(states)} states and transitions:\n' + '-'*80)
    for x in states:
        print(x)
        print('-'*80)


def pd_add_argparsers(subparsers: argparse._SubParsersAction) -> List[argparse.ArgumentParser]:
    forward_explore_inv_subparser = subparsers.add_parser('pd-forward-explore', help='Forward explore program w.r.t. its invariant')
    forward_explore_inv_subparser.set_defaults(main=forward_explore_inv)
    return [forward_explore_inv_subparser]
