'''
This file contains code for the Primal Dual research project
'''

from __future__ import annotations

import argparse
from itertools import product, chain, combinations

from syntax import *
from logic import *

from typing import TypeVar, Iterable, FrozenSet, Union

A = TypeVar('A')
# form: https://docs.python.org/3/library/itertools.html#itertools-recipes
def powerset(iterable: Iterable[A]) -> Iterator[Tuple[A, ...]]:
    'powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)'
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))


State = Model

# Here's a hacky way to eval a possibly-quantified z3 expression.
# This function only works if e is either quantifier free, or has exactly one quantifier
# (with arbitrarily many bound vars) at the root of the expression.  For example, this
# function will not work on the conjunction of two universally quantified clauses.
def eval_quant(m: z3.ModelRef, e: z3.ExprRef) -> bool:
    def ev(e: z3.ExprRef) -> bool:
        ans = m.eval(e)
        assert z3.is_bool(ans)
        assert z3.is_true(ans) or z3.is_false(ans), f'{m}\n{"="*80}\n{e}'
        return bool(ans)
    if not isinstance(e, z3.QuantifierRef):
        return ev(e)
    else:
        q = all if e.is_forall() else any
        return q(ev(z3.substitute_vars(e.body(), *tup)) for tup in product(*(
            m.get_universe(e.var_sort(i)) for i in range(e.num_vars() - 1, -1, -1) # de Bruijn
        )))


_cache_eval_in_state : Dict[Any,Any] = dict(h=0,m=0)
def eval_in_state(s: Solver, m: State, p: Expr) -> bool:
    cache = _cache_eval_in_state
    k = (m, p)
    if k not in cache:
        cache[k] = eval_quant(m.z3model, s.get_translator(m.keys[0]).translate_expr(p))
        cache['m'] += 1
        if len(cache) % 1000 == 1:
            print(f'_cache_eval_in_state length is {len(cache)}, h/m is {cache["h"]}/{cache["m"]}')
    else:
        cache['h'] += 1
    return cache[k]

_cache_two_state_implication : Dict[Any,Any] = dict(h=0,r=0)
_cache_transitions: List[Tuple[State,State]] = []
def check_two_state_implication(
        s: Solver,
        prog: Program,
        precondition: Union[Iterable[Expr], State],
        p: Expr
) -> Optional[Tuple[State,State]]:
    if not isinstance(precondition, State):
        precondition = tuple(precondition)
    k = (precondition, p)
    cache = _cache_two_state_implication
    if k not in cache:
        for prestate, poststate in _cache_transitions:
            if ((prestate == precondition if isinstance(precondition, State) else
                 all(eval_in_state(s, prestate, q) for q in precondition)) and
                not eval_in_state(s, poststate, p)):
                cache[k] = (prestate, poststate)
                cache['r'] += 1
                break
        else:
            res = check_two_state_implication_all_transitions(
                s, prog,
                [precondition.as_onestate_formula(0)] if isinstance(precondition, State) else precondition,
                p)
            if res is None:
                cache[k] = None
            else:
                z3m, _ = res
                prestate = Model(prog, z3m, s, [KEY_OLD])
                poststate = Model(prog, z3m, s, [KEY_NEW, KEY_OLD])
                result = (prestate, poststate)
                _cache_transitions.append(result)
                cache[k] = result
        if len(cache) % 10 == 1:
            print(f'_cache_two_state_implication length is {len(cache)}, h/r is {cache["h"]}/{cache["r"]}')
    else:
        cache['h'] += 1
    return cache[k]


def alpha_from_clause(s:Solver, states: Iterable[State] , top_clause:Expr) -> Sequence[Expr]:
    assert isinstance(top_clause, QuantifierExpr)
    assert isinstance(top_clause.body, NaryExpr)
    assert top_clause.body.op == 'OR'
    #assert set(top_clause.body.free_ids()) == set(v.name for v in top_clause.binder.vs)
    literals = top_clause.body.args
    assert len(set(literals)) == len(literals)

    result: List[Expr] = []
    implied : Set[FrozenSet[Expr]] = set()
    P = list(powerset(literals))
    # print(f'the top clause is {top_clause}')
    print(f'the powerset is of size {len(P)}')
    assert len(P) < 10**6, 'Really?'
    for lits in P:
        if any(s <= set(lits) for s in implied):
            continue
        vs = [v for v in top_clause.binder.vs
             if v.name in set(n for lit in lits for n in lit.free_ids())]
        if len(vs) > 0:
            clause : Expr = Forall(vs, Or(*lits))
        else:
            clause = Or(*lits)
        if all(eval_in_state(s, m, clause) for m in states):
            # z3.is_true(m.z3model.eval(s.get_translator(m.keys[0]).translate_expr(clause))) for m in states):
            result.append(clause)
            implied.add(frozenset(lits))
    return result


def alpha_from_predicates(s:Solver, states: Iterable[State] , predicates: Iterable[Expr]) -> Sequence[Expr]:
    return tuple(p for p in predicates if all(eval_in_state(s, m, p) for m in states))


def forward_explore(s: Solver,
                    prog: Program,
                    alpha: Callable[[Iterable[State]], Sequence[Expr]],
                    states: Optional[Iterable[State]] = None
) -> Tuple[Sequence[State], Sequence[Expr]]:

    if states is None:
        states = []
    else:
        states = list(states)
    a = alpha(states)
    inits = tuple(init.expr for init in prog.inits())

    changes = True
    while changes:
        changes = False

        # check for initial states violating a
        print('alpha is:')
        for e in a:
            print(f'  {e}')
        print(f'Checking if init implies everything ({len(a)} predicates)... ', end='')

        z3m = check_implication(s, inits, a)
        if z3m is not None:
            print('NO')
            m = Model(prog, z3m, s, [KEY_ONE])
            print('-'*80 + '\n' + str(m) + '\n' + '-'*80)
            states.append(m)
            changes = True
            a = alpha(states)
            continue
        else:
            print('YES')

        # check for 1 transition from an initial state or a non-initial state in states
        for precondition, p in product(chain([None], (s for s in states if len(s.keys) > 1)), a):
            print(f'Checking if {"init" if precondition is None else "state"} satisfies WP of {p}... ',end='')
            res = check_two_state_implication(
                s, prog,
                inits if precondition is None else precondition,
                p
            )
            # print(res)
            if res is not None:
                print('NO')
                _, m = res
                print('-'*80 + '\n' + str(m) + '\n' + '-'*80)
                states.append(m)
                changes = True
                a = alpha(states)
                break
            else:
                print('YES')

    # here init U states |= a, post(init U states) |= a
    # here init U states |= a /\ wp(a)

    #print(states)
    #print(a)
    return states, a


def forward_explore_inv(s: Solver, prog: Program) -> None:
    #invs = list(itertools.chain(*(as_clauses(inv.expr) for inv in prog.invs())))
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

def dedup_equivalent_predicates(s: Solver, prog: Program, itr: Iterable[Expr]) -> Sequence[Expr]:
    ans: List[Expr] = []
    for x in itr:
        for y in ans:
            if (check_implication(s, [x], [y]) is None and
                check_implication(s, [y], [x]) is None):
                break
        else:
            ans.append(x)

    return ans

def repeated_houdini(s: Solver, prog: Program) -> str:
    '''The (proof side) repeated Houdini algorith, either sharp or not.
    '''
    sharp = utils.args.sharp
    safety = tuple(inv.expr for inv in prog.invs() if inv.is_safety)
    reachable_states : Sequence[State] = ()
    clauses : List[Expr] = list(itertools.chain(*(as_clauses(x) for x in safety)))  # all top clauses in our abstraction, TODO: really convert safety to CNF
    sharp_predicates : Sequence[Expr] = ()  # the sharp predicates (minimal clauses true on the known reachable states)
    def alpha_clauses(states: Iterable[State]) -> Sequence[Expr]:
        return sorted(
            dedup_equivalent_predicates(s, prog, chain(*(alpha_from_clause(s, states, clause) for clause in clauses))),
            key=lambda x: (len(str(x)),str(x))
        )
    def alpha_sharp(states: Iterable[State]) -> Sequence[Expr]:
        return sorted(
            alpha_from_predicates(s, states, sharp_predicates),
            key=lambda x: (len(str(x)),str(x))
        )
    while True:
        reachable_states, a = forward_explore(s, prog, alpha_clauses, reachable_states)
        print(f'Current reachable states ({len(reachable_states)}):')
        for m in reachable_states:
            print(str(m) + '\n' + '-'*80)
        if check_implication(s, a, safety) is not None:
            print('Found safety violation!')
            return 'UNSAFE'
        sharp_predicates = tuple(a)
        print(f'Current sharp predicates ({len(sharp_predicates)}):')
        for p in sharp_predicates:
            print(p)
        states = reachable_states
        unreachable = []
        while True:
            for p in a:
                res = check_two_state_implication(s, prog, a, p)
                if res is not None:
                    print(f'Found new CTI violating {p}')
                    prestate, poststate = res
                    print('-'*80 + '\n' + str(poststate) + '\n' + '-'*80)
                    unreachable.append(prestate)
                    states, a = forward_explore(
                        s, prog,
                        alpha_sharp if sharp else alpha_clauses,
                        chain(states, [prestate, poststate]) # so that forward_explore also considers extensions of the prestate
                    )
                    break
            else:
                break
        if len(a) > 0 and check_implication(s, a, safety) is None:
            print(f'Inductive invariant found with {len(a)} predicates:')
            for p in sorted(a, key=lambda x: len(str(x))):
                print(p)
            return 'SAFE'
        else:
            print(f'Refining by {len(unreachable)} new clauses:')
            for m in unreachable:
                new_clauses = as_clauses(Not(m.as_diagram(0).to_ast()))
                print(new_clauses[0])
                clauses.extend(new_clauses)
            print('='*80)


def add_argparsers(subparsers: argparse._SubParsersAction) -> Iterable[argparse.ArgumentParser]:
    result : List[argparse.ArgumentParser] = []

    # forward_explore_inv
    s = subparsers.add_parser('pd-forward-explore', help='Forward explore program w.r.t. its invariant')
    s.set_defaults(main=forward_explore_inv)
    result.append(s)

    # repeated_houdini
    s = subparsers.add_parser('pd-repeated-houdini', help='Run the repeated Houdini algorith in the proof space')
    s.set_defaults(main=repeated_houdini)
    s.add_argument('--sharp', action=utils.YesNoAction, default=True,
                   help='search for sharp invariants')
    result.append(s)

    return result
