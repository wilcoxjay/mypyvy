'''
This file contains code for the Primal Dual research project
'''

from __future__ import annotations

from itertools import product, chain, combinations

from syntax import *
from logic import *

from typing import TypeVar, Iterable, FrozenSet

A = TypeVar('A')
# form: https://docs.python.org/3/library/itertools.html#itertools-recipes
def powerset(iterable: Iterable[A]) -> Iterator[Tuple[A, ...]]:
    'powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)'
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))


State = Model

_cache_eval_in_state : Dict[Any,Any] = dict(h=0,m=0)
def eval_in_state(s: Solver, m: State, p: Expr) -> bool:
    cache = _cache_eval_in_state
    k = (m, p)
    if k not in cache:
        cache[k] = check_implication(s, [m.as_onestate_formula(0)], [p]) is None
        cache['m'] += 1
        if len(cache) % 1000 == 1:
            print(f'_cache_eval_in_state length is {len(cache)}, h/m is {cache["h"]}/{cache["m"]}')
    else:
        cache['h'] += 1
    return cache[k]

_cache_check_two_state_implication_all_transitions_cache : Dict[Any,Any] = dict(h=0,m=0)
def _check_two_state_implication_all_transitions(
        s: Solver,
        prog: Program,
        precondition: Iterable[Expr],
        p: Expr
) -> Optional[Tuple[z3.ModelRef, DefinitionDecl]]:
    k = (tuple(precondition), p)
    cache = _cache_check_two_state_implication_all_transitions_cache
    if k not in cache:
        cache[k] = check_two_state_implication_all_transitions(s, prog, precondition, p)
        cache['m'] += 1
        if len(cache) % 10 == 1:
            print(f'_cache_check_two_state_implication_all_transitions_cache length is {len(cache)}, h/m is {cache["h"]}/{cache["m"]}')
    else:
        cache['h'] += 1
    return cache[k]


def alpha_from_clause(s:Solver, states: List[State] , top_clause:Expr) -> List[Expr]:
    assert isinstance(top_clause, QuantifierExpr)
    assert isinstance(top_clause.body, NaryExpr)
    assert top_clause.body.op == 'OR'
    #assert set(top_clause.body.free_ids()) == set(v.name for v in top_clause.binder.vs)
    literals = top_clause.body.args
    assert len(set(literals)) == len(literals)

    result: List[Expr] = []
    implied : Set[FrozenSet[Expr]] = set()
    for lits in powerset(literals):
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


def alpha_from_predicates(s:Solver, states: List[State] , predicates: Sequence[Expr]) -> Sequence[Expr]:
    return tuple(p for p in predicates if all(eval_in_state(s, m, p) for m in states))


def forward_explore(s: Solver,
                    prog: Program,
                    alpha: Callable[[List[State]], List[Expr]],
                    states: Optional[Iterable[State]] = None
) -> Tuple[List[State], List[Expr]]:

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

        # check for 1 transition from an initial state or a state in states
        for prestate, p in product(chain([None], states), a):
            print(f'Checking if {"init" if prestate is None else "state"} satisfies WP of {p}... ',end='')
            if prestate is None:
                precondition = inits
            else:
                precondition = (prestate.as_onestate_formula(0),)
            res = _check_two_state_implication_all_transitions(s, prog, precondition, p)
            # print(res)
            if res is not None:
                print('NO')
                z3m, ition = res
                m = Model(prog, z3m, s, [KEY_NEW, KEY_OLD])
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
    #invs = [as_clause(inv.expr) for inv in prog.invs()]
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


def repeated_houdini(s: Solver, prog: Program) -> None:
    clauses = [as_clause(inv.expr) for inv in prog.invs() if inv.is_safety]
    alpha  = lambda states: sorted(set(chain(*(alpha_from_clause(s, states, clause) for clause in clauses))), key=lambda x: (len(str(x)),str(x)))

    reachable_states, a = forward_explore(s, prog, alpha)
    while True:
        #open('_.dat', 'w').write(repr(dict(clauses=clauses, reachable_states=reachable_states)))
        reachable_states, a = forward_explore(s, prog, alpha, reachable_states)
        print(f'Discovered {len(reachable_states)} reachable states:')
        for m in reachable_states:
            print(str(m) + '\n' + '-'*80)
        states = list(reachable_states)
        unreachable = []
        while True:
            for p in a:
                res = _check_two_state_implication_all_transitions(s, prog, a, p)
                if res is not None:
                    print(f'Found new CTI violating {p}')
                    z3m, ition = res
                    m = Model(prog, z3m, s, [KEY_NEW, KEY_OLD])
                    print('-'*80 + '\n' + str(m) + '\n' + '-'*80)
                    unreachable.append(m)
                    states.append(m)
                    states, a = forward_explore(s, prog, alpha, states)
                    changes = True
                    break
            else:
                break
        if len(unreachable) == 0:
            print(f'Inductive invariant found with {len(a)} predicates:')
            for p in sorted(a, key=lambda x: len(str(x))):
                print(p)
            break
        else:
            print(f'Refining by {len(unreachable)} new clauses:')
            for m in unreachable:
                clause = as_clause(Not(m.as_diagram(1).to_ast()))
                print(clause)
                clauses.append(clause)
            print('='*80)
            #print(f'Abstraction now contains {len(alpha([]))} predicates')


def repeated_houdini_sharp(s: Solver, prog: Program) -> None:
    clauses = [as_clause(inv.expr) for inv in prog.invs() if inv.is_safety]
    alpha_clauses  = lambda states: sorted(set(chain(*(alpha_from_clause(s, states, clause) for clause in clauses))), key=lambda x: (len(str(x)),str(x)))

    reachable_states, a = forward_explore(s, prog, alpha_clauses)
    while True:
        #open('_.dat', 'w').write(repr(dict(clauses=clauses, reachable_states=reachable_states)))
        reachable_states, a = forward_explore(s, prog, alpha_clauses, reachable_states)
        sharp_predicates = tuple(a)
        print(f'Discovered {len(reachable_states)} reachable states:')
        for m in reachable_states:
            print(str(m) + '\n' + '-'*80)
        print(f'Discovered {len(sharp_predicates)} sharp predicates:')
        for p in sharp_predicates:
            print(p)
        alpha_sharp = lambda states: sorted(alpha_from_predicates(s, states, sharp_predicates), key=lambda x: (len(str(x)),str(x)))
        states = list(reachable_states)
        unreachable = []
        while True:
            for p in a:
                res = _check_two_state_implication_all_transitions(s, prog, a, p)
                if res is not None:
                    print(f'Found new CTI violating {p}')
                    z3m, ition = res
                    m = Model(prog, z3m, s, [KEY_NEW, KEY_OLD])
                    print('-'*80 + '\n' + str(m) + '\n' + '-'*80)
                    unreachable.append(m)
                    states.append(m)
                    states, a = forward_explore(s, prog, alpha_sharp, states)
                    changes = True
                    break
            else:
                break
        if len(unreachable) == 0:
            print(f'Inductive invariant found with {len(a)} predicates:')
            for p in sorted(a, key=lambda x: len(str(x))):
                print(p)
            break
        else:
            print(f'Refining by {len(unreachable)} new clauses:')
            for m in unreachable:
                clause = as_clause(Not(m.as_diagram(1).to_ast()))
                print(clause)
                clauses.append(clause)
            print('='*80)
            #print(f'Abstraction now contains {len(alpha([]))} predicates')
