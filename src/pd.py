'''
This file contains code for the Primal Dual research project
'''

from __future__ import annotations

import argparse
from itertools import product, chain, combinations

from syntax import *
from logic import *

from typing import TypeVar, Iterable, FrozenSet, Union, Callable, Generator, Set, Optional

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
        ans = m.eval(e)#, model_completion=True)
        assert z3.is_bool(ans)
        assert z3.is_true(ans) or z3.is_false(ans), f'{m}\n{"="*80}\n{e}\n{"="*80}\n{ans}'
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
        if m.z3model is not None:
            cache[k] = eval_quant(m.z3model, s.get_translator(m.keys[0]).translate_expr(p))
        else:
            cache[k] = check_implication(s, [m.as_onestate_formula(0)], [p]) is None

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
                prestate = Model.from_z3(prog, s, [KEY_OLD], z3m)
                poststate = Model.from_z3(prog, s, [KEY_NEW, KEY_OLD], z3m)
                result = (prestate, poststate)
                _cache_transitions.append(result)
                cache[k] = result
        if len(cache) % 100 == 1:
            print(f'_cache_two_state_implication length is {len(cache)}, h/r is {cache["h"]}/{cache["r"]}')
    else:
        cache['h'] += 1
    return cache[k]


class MapSolver(object):
    def __init__(self, n: int):
        """Initialization.
             Args:
            n: The number of constraints to map.
        """
        self.solver = z3.Solver()
        self.n = n
        self.all_n = set(range(n))  # used in complement fairly frequently

    def next_seed(self) -> Optional[Set[int]]:
        """Get the seed from the current model, if there is one.
            Returns:
            A seed as an array of 0-based constraint indexes.
        """
        if self.solver.check() == z3.unsat:
            return None
        seed = self.all_n.copy()  # default to all True for "high bias"
        model = self.solver.model()
        for x in model:
            if z3.is_false(model[x]):
                seed.remove(int(x.name()))
        return set(seed)

    def block_down(self, frompoint: Set[int]) -> None:
        """Block down from a given set."""
        comp = self.all_n - frompoint
        self.solver.add(z3.Or(*(z3.Bool(str(i)) for i in comp)))

    def block_up(self, frompoint: Set[int]) -> None:
        """Block up from a given set."""
        self.solver.add(z3.Or(*(z3.Not(z3.Bool(str(i))) for i in frompoint)))


def marco(n: int, f: Callable[[Set[int]], bool]) -> Generator[Tuple[str,Set[int]], None, None]:
    """Basic MUS/MCS enumeration, as a simple example."""
    def shrink(seed: Set[int]) -> Set[int]:
        assert f(seed)
        current = set(seed)
        for i in sorted(seed):
            if i not in current:
                assert False # this can happen once we have "unsat cores" from f
                continue
            if f(current - {i}):
                current.remove(i)
        return current

    def grow(seed: Set[int]) -> Set[int]:
        assert not f(seed)
        current = seed
        for i in sorted(set(range(n)) - set(seed)):
            if not f(current | {i}):
                current.add(i)
        return current

    msolver = MapSolver(n)
    while True:
        seed = msolver.next_seed()
        if seed is None:
           return
        if not f(seed):
           MSS = grow(seed)
           yield ("MSS", MSS)
           msolver.block_down(MSS)
        else:
           MUS = shrink(seed)
           yield ("MUS", MUS)
           msolver.block_up(MUS)


def alpha_from_clause_marco(solver:Solver, states: Iterable[State] , top_clause:Expr) -> Sequence[Expr]:
    # TODO: why can't top_clause be quantifier free?
    assert isinstance(top_clause, QuantifierExpr)
    assert isinstance(top_clause.body, NaryExpr)
    assert top_clause.body.op == 'OR'
    #assert set(top_clause.body.free_ids()) == set(v.name for v in top_clause.binder.vs)
    literals = tuple(top_clause.body.args) # TODO: cannot sort sorted(top_clause.body.args)
    variables = tuple(top_clause.binder.vs)
    assert len(set(literals)) == len(literals)
    n = len(literals)
    print(f'the powerset is of size {2**n}', end='...\n')

    def to_clause(s: Set[int]) -> Expr:
        lits = [literals[i] for i in s]
        vs = [v for v in variables if v.name in set(n for lit in lits for n in lit.free_ids())]
        if len(vs) > 0:
            return Forall(vs, Or(*lits))
        else:
            return Or(*lits)

    def f(s: Set[int]) -> bool:
        clause = to_clause(s)
        return all(eval_in_state(solver, m, clause) for m in states)

    result: List[Expr] = []
    for k, v in marco(n, f):
        if k == 'MUS':
            result.append(to_clause(v))
            print(f'  {len(result)}: {result[-1]}')
    print(f'alpha is of size {len(result)}')
    return result


def alpha_from_clause(solver:Solver, states: Iterable[State] , top_clause:Expr) -> Sequence[Expr]:
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
        if all(eval_in_state(solver, m, clause) for m in states):
            result.append(clause)
            implied.add(frozenset(lits))
    return result
alpha_from_clause = alpha_from_clause_marco


def alpha_from_predicates(s:Solver, states: Iterable[State] , predicates: Iterable[Expr]) -> Sequence[Expr]:
    return tuple(p for p in predicates if all(eval_in_state(s, m, p) for m in states))



def forward_explore_marco(solver: Solver,
                          prog: Program,
                          clauses: Sequence[Expr],
                          _states: Optional[Iterable[State]] = None
) -> Tuple[Sequence[State], Sequence[Expr]]:

    states: List[State] = [] if _states is None else list(_states)

    inits = tuple(init.expr for init in prog.inits())

    class SubclausesMap(object):
        def __init__(self, top_clause: Expr):
            # TODO: why can't top_clause be quantifier free?
            assert isinstance(top_clause, QuantifierExpr)
            assert isinstance(top_clause.body, NaryExpr)
            assert top_clause.body.op == 'OR'
            self.literals = tuple(top_clause.body.args)
            self.variables = tuple(top_clause.binder.vs)
            self.n = len(self.literals)
            self.all_n = set(range(self.n))  # used in complement fairly frequently
            #self.satisfied : List[Sequence[int]] = []
            #self.violated : List[Sequence[int]] = []
            #self.wp_satisfied : List[Sequence[int]] = []
            #self.wp_violated : List[Sequence[int]] = []
            self.blocked_up : List[Set[int]] = []
            self.blocked_down : List[Set[int]] = []
            self.reset_solver([], [])

        def reset_solver(self, up: List[Set[int]], down: List[Set[int]]) -> None:
            self.solver = z3.Solver()
            self.blocked_up = []
            self.blocked_down = []
            for s in up:
                self.block_up(s)
            for s in down:
                self.block_down(s)
            assert self.blocked_up == up
            assert self.blocked_down == down

        def next_seed(self, bias: bool = False) -> Optional[Set[int]]:
            """Get the seed from the current model, if there is one.
                Returns:
                A seed as an array of 0-based constraint indexes.
            """
            if self.solver.check() == z3.unsat:
                return None
            m = self.solver.model()
            if bias:
                # default to all True for "high bias"
                return self.all_n - set(
                    int(x.name())
                    for x in m
                    if z3.is_false(m[x])
                )
            else:
                # default to all False for "low bias"
                result = set(
                    int(x.name())
                    for x in m
                    if z3.is_true(m[x])
                )
                # minimize further
                forced_to_false = list(self.all_n - result)
                for i in range(self.n):
                    if i not in forced_to_false and self.solver.check(*(z3.Not(z3.Bool(str(j))) for j in chain(forced_to_false, [i]))) == z3.sat:
                        forced_to_false.append(i)
                assert self.solver.check(*(z3.Not(z3.Bool(str(j))) for j in forced_to_false)) == z3.sat
                return self.all_n - set(forced_to_false)

        def block_down(self, frompoint: Set[int]) -> None:
            """Block down from a given set."""
            self.blocked_down.append(set(frompoint))
            comp = self.all_n - frompoint
            self.solver.add(z3.Or(*(z3.Bool(str(i)) for i in comp)))

        def block_up(self, frompoint: Set[int]) -> None:
            """Block up from a given set."""
            self.blocked_up.append(set(frompoint))
            self.solver.add(z3.Or(*(z3.Not(z3.Bool(str(i))) for i in frompoint)))

        def to_clause(self, s: Set[int]) -> Expr:
            lits = [self.literals[i] for i in sorted(s)]
            free = set(chain(*(lit.free_ids() for lit in lits)))
            vs = [v for v in self.variables if v.name in free]
            return Forall(vs, Or(*lits)) if len(vs) > 0 else Or(*lits)

    def valid(clause: Expr) -> bool:
        # return True iff clause is implied by init and valid in all states
        # when returning False, possibly learn a new state
        if not all(eval_in_state(solver, m, clause) for m in states):
            return False
        z3m = check_implication(solver, inits, [clause])
        if z3m is not None:
            print(f'Checking if init implies: {clause}... NO')
            print('Found new initial state:')
            m = Model.from_z3(prog, solver, [KEY_ONE], z3m)
            print('-'*80 + '\n' + str(m) + '\n' + '-'*80)
            states.append(m)
            return False
        return True

    def wp_valid(clause: Expr) -> bool:
        # return True iff wp(clause) is implied by init and valid in all states
        # when returning False, add a new transition to states
        # assert valid(clause)
        for precondition in chain((s for s in states), [None]): # TODO: why len(s.keys) > 1 ?
            #print(f'Checking if {"init" if precondition is None else "state"} satisfies WP of {clause}... ',end='')
            res = check_two_state_implication(
                solver,
                prog,
                inits if precondition is None else precondition,
                clause
            )
            if res is not None:
                print(f'Checking if {"init" if precondition is None else "state"} satisfies WP of {clause}... ',end='')
                print('NO\nFound new transition:')
                prestate, poststate = res
                print('-'*80 + '\n' + str(poststate) + '\n' + '-'*80)
                if precondition is None:
                    states.append(prestate)
                states.append(poststate)
                return False
            else:
                #print('YES')
                pass
        return True

    N = len(clauses)
    maps = [SubclausesMap(top_clause) for top_clause in clauses]
    a: List[Expr] = [] # set of clauses such that: init U states |= a /\ wp(a)
    for rotate in itertools.count(0):
        # for p in a:
        #     assert valid(p) and wp_valid(p)

        for i in range(len(maps)):
            mp = maps[(rotate + i) % N]
            seed = mp.next_seed()
            if seed is not None:
                break
        else:
            # here init U states |= a /\ wp(a), and also there is no uncharted territory in the maps
            #print(states)
            #print(a)
            return states, dedup_equivalent_predicates(solver, prog, a)

        n_states = len(states)

        if not valid(mp.to_clause(seed)):
            # the clause is not valid, grow and block it
            current = seed
            for i in sorted(mp.all_n - seed):
                if not valid(mp.to_clause(current | {i})):
                    current.add(i)
            # assert not valid(mp.to_clause(current))
            mp.block_down(current)
            # this may have added new (initial) states

        elif not wp_valid(mp.to_clause(seed)):
            # the clause is was valid, but its wp was not. we already learned a new state so now its not even valid
            # grow the clause (while learning new sates)
            assert len(states) > n_states
            current = seed
            for i in sorted(mp.all_n - seed):
                cl = mp.to_clause(current | {i})
                if not (valid(cl) and wp_valid(cl)):
                    current.add(i)
            # assert not valid(mp.to_clause(current))
            mp.block_down(current)
            # this surely added new states

        else:
            # the clause is valid, and its wp is also valid
            # shrink it, but ignore new states from failed minimizations (TODO: does that make sense?)
            print(f'shrinking from {len(seed)}... ', end='')
            current = set(seed)
            for i in sorted(seed):
                if i not in current:
                    assert False # this can happen once we have "unsat cores" from f
                    continue
                cl = mp.to_clause(current - {i})
                if valid(cl) and wp_valid(cl):
                    current.remove(i)
                else:
                    # we don't really want to learn any new states when shrinking, so discard what we found
                    states = states[:n_states]
            print(f'to {len(current)}')
            cl = mp.to_clause(current)
            # assert valid(cl) and wp_valid(cl)
            assert len(states) == n_states
            a.append(cl)
            mp.block_up(current)

        # maintain a and the solver in case we added new states
        if len(states) > n_states:
             # TODO: do something smarter
            print(f'forward_explore_marco a was {len(a)} predicates, resetting')
            a = []
            for mp in maps:
                mp.reset_solver(up=[], down=mp.blocked_down)
    assert False


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
        print(f'a is ({len(a)} predicates):' if len(a) > 0 else 'a is true')
        for e in a:
            print(f'  {e}')
        print(f'Checking if init implies everything ({len(a)} predicates)... ', end='')

        z3m = check_implication(s, inits, a)
        if z3m is not None:
            print('NO')
            m = Model.from_z3(prog, s, [KEY_ONE], z3m)
            print('-'*80 + '\n' + str(m) + '\n' + '-'*80)
            states.append(m)
            changes = True
            a = alpha(states)
            continue
        else:
            print('YES')

        # check for 1 transition from an initial state or a non-initial state in states
        for precondition, p in product(chain([None], (s for s in states if len(s.keys) > 1)), a):
            # print(f'Checking if {"init" if precondition is None else "state"} satisfies WP of {p}... ',end='')
            res = check_two_state_implication(
                s, prog,
                inits if precondition is None else precondition,
                p
            )
            # print(res)
            if res is not None:
                print(f'Checking if {"init" if precondition is None else "state"} satisfies WP of {p}... ',end='')
                print('NO')
                _, m = res
                print('-'*80 + '\n' + str(m) + '\n' + '-'*80)
                states.append(m)
                changes = True
                a = alpha(states)
                break
            else:
                # print('YES')
                pass

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
    ps = list(itr)
    print(f'Deduping {len(ps)} predicates to...',end=' ')
    sys.stdout.flush()
    ans: List[Expr] = []
    for x in ps:
        for y in ans:
            if x == y:# or (check_implication(s, [x], [y], never_minimize=True) is None and
                      #    check_implication(s, [y], [x], never_minimize=True) is None):
                break
        else:
            ans.append(x)
    print(f'{len(ans)} predicates')
    return ans

def repeated_houdini(s: Solver, prog: Program) -> str:
    '''The (proof side) repeated Houdini algorith, either sharp or not.
    '''
    sharp = utils.args.sharp
    safety = tuple(inv.expr for inv in prog.invs() if inv.is_safety)
    reachable_states : Sequence[State] = ()
    clauses : List[Expr] = list(itertools.chain(*(as_clauses(x) for x in safety)))  # all top clauses in our abstraction
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
        # reachable_states, a = forward_explore(s, prog, alpha_clauses, reachable_states)
        reachable_states, a = forward_explore_marco(s, prog, clauses, reachable_states)
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
        print(f'Current inductive invariant ({len(a)} predicates) is:' if len(a) > 0 else 'Current inductive invariant is true')
        for p in sorted(a, key=lambda x: len(str(x))):
            print(p)
        if len(a) > 0 and check_implication(s, a, safety) is None:
            print('Implies safety!')
            return 'SAFE'
        else:
            new_clauses = []
            for m in unreachable:
                cs = as_clauses(Not(m.as_diagram(0).to_ast()))
                assert len(cs) == 1
                c = cs[0]
                if c not in clauses:
                    new_clauses.append(c)
            print(f'Refining from {len(unreachable)} unreachable states which give {len(new_clauses)} new clauses:')
            for c in new_clauses:
                print(f'  {c}')
            clauses.extend(new_clauses)
            assert len(clauses) == len(set(clauses))
            assert clauses == list(dedup_equivalent_predicates(s, prog, clauses))
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
