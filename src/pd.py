'''
This file contains code for the Primal Dual research project
'''

from __future__ import annotations

import argparse
from itertools import product, chain, combinations, repeat
from collections import defaultdict
from pathlib import Path
import pickle
import sys
import math

from syntax import *
from logic import *

from typing import TypeVar, Iterable, FrozenSet, Union, Callable, Generator, Set, Optional, cast, Type

A = TypeVar('A')
# form: https://docs.python.org/3/library/itertools.html#itertools-recipes
def powerset(iterable: Iterable[A]) -> Iterator[Tuple[A, ...]]:
    'powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)'
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))


State = Model

cache_path: Optional[Path] = None

def dump_caches() -> None:
    if cache_path is not None:
        caches = [
            '_cache_eval_in_state',
            '_cache_two_state_implication',
            '_cache_transitions',
            '_cache_initial',
        ]
        cache = {k: sys.modules['pd'].__dict__[k] for k in caches}
        print('dumping caches:', *(f'{k}:{len(cache[k])}' for k in sorted(cache)), end=' ... ')
        with open(cache_path, 'wb') as cache_file:
            pickle.dump(cache, cache_file)
        print('done')

def load_caches() -> None:
    if cache_path is not None and cache_path.exists():
        print(f'loading caches from {cache_path!r}', end='... ')
        sys.stdout.flush()
        with open(cache_path, 'rb') as cache_file:
            cache = pickle.load(cache_file)
        print('loaded caches:', *(f'{k}:{len(cache[k])}' for k in sorted(cache)))
        if utils.args.clear_cache:
            print('clearing caches')
            cache = {}
        elif utils.args.clear_cache_memo:
            to_clear = [k for k, v in cache.items() if isinstance(v, dict)]
            print(f'clearing memoization caches:', *sorted(to_clear))
            for k in to_clear:
                del cache[k]
        sys.modules['pd'].__dict__.update(cache)


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
            # dump_caches()
            print(f'_cache_eval_in_state length is {len(cache)}, h/m is {cache["h"]}/{cache["m"]}')
    else:
        cache['h'] += 1
    return cache[k]

_cache_initial: List[State] = []
# TODO: could also cache expressions already found to be initial
def check_initial(solver: Solver, p: Expr) -> Optional[Model]:
    prog = syntax.the_program
    inits = tuple(init.expr for init in prog.inits())
    for s in _cache_initial:
        if not eval_in_state(solver, s, p):
            print(f'Found cached initial state violating {p}:')
            print('-'*80 + '\n' + str(s) + '\n' + '-'*80)
            return s
    z3m = check_implication(solver, inits, [p])
    if z3m is not None:
        if utils.args.cache_only or utils.args.cache_only_discovered:
            print(f'loudly describing this unexpected cache miss for predicate {p} on init:')
            for s in _cache_initial:
                print('-'*80 + '\n' + str(s) + '\n' + '-'*80)
                print(eval_in_state, solver, s, p)
            assert False
        s = Model.from_z3([KEY_ONE], z3m)
        _cache_initial.append(s)
        print(f'Found new initial state violating {p}:')
        print('-'*80 + '\n' + str(s) + '\n' + '-'*80)
        return s
    return None

_cache_two_state_implication : Dict[Any,Any] = dict(h=0,r=0)
_cache_transitions: List[Tuple[State,State]] = []
def isomorphic_states(solver: Solver, s: State, t: State) -> bool:
    x = s.as_onestate_formula(0)
    y = t.as_onestate_formula(0)
    return x == y # or check_implication(solver, [], [Iff(x, y)]) is None
    # TODO: we need to figure this out. are two isomorphic structures the same state or no? this showed up in:
    # time ./src/mypyvy.py pd-repeated-houdini --no-sharp --clear-cache examples/lockserv.pyv > 1
    # time ./src/mypyvy.py pd-repeated-houdini --no-sharp --clear-cache-memo --cache-only-discovered examples/lockserv.pyv > 2
    # this can be fixed by checking equivalence between onestate formulas, but this is very slow
def check_two_state_implication(
        s: Solver,
        precondition: Union[Iterable[Expr], State],
        p: Expr,
        msg: str = 'transition'
) -> Optional[Tuple[State,State]]:
    prog = syntax.the_program
    inits = tuple(init.expr for init in prog.inits())

    if not isinstance(precondition, State):
        precondition = tuple(precondition)
    k = (precondition, p)
    cache = _cache_two_state_implication
    if k not in cache:
        if utils.args.cache_only:
            print(f'loudly describing this unexpected cache miss for predicate {p} on precondition:')
            if isinstance(precondition, State):
                print('-'*80 + '\n' + str(precondition) + '\n' + '-'*80)
            else:
                print('-'*80)
                for e in precondition:
                    print(e)
                print('-'*80)
            for _k in cache:
                if isinstance(_k, tuple):
                    x, y = _k
                    if x == precondition:
                        print(y, cache[_k], y == p, hash(y), hash(p))
            assert False

        for prestate, poststate in _cache_transitions:
            # TODO: not sure if this should be ==, or alpha
            # equivalent, or some other solution by making sure that
            # the prestate of transition from state s is considered
            # the same as state s
            if ((isomorphic_states(s, prestate, precondition) if isinstance(precondition, State) else
                 all(eval_in_state(s, prestate, q) for q in precondition)) and
                not eval_in_state(s, poststate, p)):
                cache[k] = (prestate, poststate)
                cache['r'] += 1
                print(f'Found previous {msg} violating {p}:')
                print('-'*80 + '\n' + str(poststate) + '\n' + '-'*80)
                break
        else:
            res = check_two_state_implication_all_transitions(
                s,
                [precondition.as_onestate_formula(0)] if isinstance(precondition, State) else precondition,
                p)
            if res is None:
                cache[k] = None
            else:
                if utils.args.cache_only_discovered:
                    print(f'loudly describing this unexpected cache miss for predicate {p} on precondition:')
                    if isinstance(precondition, State):
                        print('-'*80 + '\n' + str(precondition) + '\n' + '-'*80)
                    else:
                        print('-'*80)
                        for e in precondition:
                            print(e)
                        print('-'*80)
                    print('_cache_transitions:')
                    for prestate, poststate in _cache_transitions:
                        print('prestate:')
                        print('-'*80 + '\n' + str(prestate) + '\n' + '-'*80)
                        print('poststate:')
                        print('-'*80 + '\n' + str(poststate) + '\n' + '-'*80)
                        if isinstance(precondition, State):
                            print(f'prestate.as_onestate_formula(0) == precondition.as_onestate_formula(0): '
                                  f'{prestate.as_onestate_formula(0) == precondition.as_onestate_formula(0)}')
                        else:
                            print(f'all(eval_in_state(s, prestate, q) for q in precondition): '
                                  f'{all(eval_in_state(s, prestate, q) for q in precondition)}')
                        print(f'eval_in_state(s, poststate, p): {eval_in_state(s, poststate, p)}')
                    assert False
                z3m, _ = res
                prestate = Model.from_z3([KEY_OLD], z3m)
                poststate = Model.from_z3([KEY_NEW, KEY_OLD], z3m)
                result = (prestate, poststate)
                _cache_transitions.append(result)
                for state in result:
                    if all(eval_in_state(s, state, p) for p in inits):
                        _cache_initial.append(state)
                    # TODO: actually, we should first try to get (from Z3) a transition where the prestate is initial
                cache[k] = result
                print(f'Found new {msg} violating {p}:')
                print('-'*80 + '\n' + str(poststate) + '\n' + '-'*80)

        if len(cache) % 100 == 1:
            # dump_caches()
            print(f'_cache_two_state_implication length is {len(cache)}, h/r is {cache["h"]}/{cache["r"]}')
    else:
        if cache[k] is not None:
            prestate, poststate = cache[k]
            print(f'Found cached {msg} violating {p} from precondition:')
            if isinstance(precondition, State):
                print('-'*80 + '\n' + str(precondition) + '\n' + '-'*80)
            else:
                print('-'*80)
                for e in precondition:
                    print(e)
                print('-'*80)
            print('-'*80 + '\n' + str(poststate) + '\n' + '-'*80)
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
                          clauses: Sequence[Expr],
                          _states: Optional[Iterable[State]] = None
) -> Tuple[Sequence[State], Sequence[Expr]]:

    prog = syntax.the_program
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
        s = check_initial(solver, clause)
        if s is not None:
            states.append(s)
            return False
        else:
            return True

    def wp_valid(mp: SubclausesMap, s: Set[int]) -> bool:
        clause = mp.to_clause(s)
        # return True iff wp(clause) is implied by init and valid in all states
        # when returning False, add a new transition to states
        # assert valid(clause)
        for precondition in chain((s for s in states), [None]):
            res = check_two_state_implication(
                solver,
                inits if precondition is None else precondition,
                clause
            )
            if res is not None:
                prestate, poststate = res
                if precondition is None:
                    states.append(prestate)
                states.append(poststate)
                return False
        return True

    N = len(clauses)
    maps = [SubclausesMap(top_clause) for top_clause in clauses]

    # TODO: here lies commented out the version that uses one big
    # solver, since it does not use caches appropriately. Maybe we
    # should bring this back at some point
    #
    # wp_valid_solver = Solver()
    # t = wp_valid_solver.get_translator(KEY_NEW, KEY_OLD)
    # mp_indicators: Dict[SubclausesMap, z3.ExprRef] = {mp: z3.Bool(f'@mp_{i}') for i, mp in enumerate(maps)}
    # lit_indicators: Sequence[z3.ExprRef] = tuple(z3.Bool(f'@lit_{i}') for i in range(max(mp.n for mp in maps)))
    # for mp in maps:
    #     # there is some craziness here about mixing a mypyvy clause with z3 indicator variables
    #     # some of this code is taken out of syntax.Z3Translator.translate_expr
    #     # TODO: why can't top clause be quantifier free? it should be possible
    #     top_clause = mp.to_clause(mp.all_n)
    #     assert isinstance(top_clause, QuantifierExpr)
    #     assert isinstance(top_clause.body, NaryExpr)
    #     assert top_clause.body.op == 'OR'
    #     assert tuple(mp.literals) == tuple(top_clause.body.args)
    #     bs = t.bind(top_clause.binder)
    #     with t.scope.in_scope(top_clause.binder, bs):
    #         body = z3.Or(*(
    #             z3.And(lit_indicators[i], t.translate_expr(lit))
    #             for i, lit in enumerate(mp.literals)
    #         ))
    #     wp_valid_solver.add(z3.Implies(mp_indicators[mp], z3.Not(z3.ForAll(bs, body))))
    # init_indicator = z3.Bool('@init')
    # for init in prog.inits():
    #     wp_valid_solver.add(z3.Implies(init_indicator, t.translate_expr(init.expr, old=True)))
    # precondition_indicators: Dict[Optional[State], z3.ExprRef] = {None: init_indicator}
    # def precondition_indicator(precondition: Optional[State]) -> z3.ExprRef:
    #     if precondition not in precondition_indicators:
    #         assert precondition is not None
    #         x = z3.Bool(f'@state_{id(precondition)})')
    #         wp_valid_solver.add(z3.Implies(x, t.translate_expr(precondition.as_onestate_formula(0), old=True)))
    #         precondition_indicators[precondition] = x
    #     return precondition_indicators[precondition]
    # transition_indicators = []
    # for i, trans in enumerate(prog.transitions()):
    #     transition_indicators.append(z3.Bool(f'@transition_{i}'))
    #     wp_valid_solver.add(z3.Implies(transition_indicators[i], t.translate_transition(trans)))
    # wp_checked_valid: Set[Tuple[Optional[State], SubclausesMap, Tuple[int,...]]] = set()
    # def wp_valid(mp: SubclausesMap, s: Set[int]) -> bool:
    #     # return True iff wp(clause) is implied by init and valid in all states
    #     # when returning False, add a new transition to states
    #     # assert valid(clause)
    #     for precondition in chain((s for s in states), [None]):
    #         k = (precondition, mp, tuple(s))
    #         if k in wp_checked_valid:
    #             continue
    #         for transition_indicator in transition_indicators:
    #             #print(f'Checking if {"init" if precondition is None else "state"} satisfies WP of {clause}... ',end='')
    #             indicators = (
    #                 precondition_indicator(precondition),
    #                 transition_indicator,
    #                 mp_indicators[mp],
    #             ) + tuple(lit_indicators[i] for i in sorted(s))
    #             print(f'checking {indicators}... ', end='')
    #             z3res = wp_valid_solver.check(indicators)
    #             print('', end='\r')
    #             assert z3res == z3.unsat or z3res == z3.sat
    #             if z3res == z3.unsat:
    #                 # learn it for next time (TODO maybe z3 already does it)
    #                 # TODO: maybe get unsat core, or even minimal unsat core
    #                 wp_valid_solver.add(z3.Or(*(z3.Not(x) for x in indicators)))
    #             else:
    #                 z3model = wp_valid_solver.model(indicators)
    #                 # assert all(not z3.is_false(z3model.eval(x)) for x in indicators), (indicators, z3model)
    #                 prestate = Model.from_z3([KEY_OLD], z3model)
    #                 poststate = Model.from_z3([KEY_NEW, KEY_OLD], z3model)
    #                 _cache_transitions.append((prestate, poststate))
    #                 print(f'{"init" if precondition is None else "state"} violates WP of {mp.to_clause(s)}')
    #                 print('Found new transition:')
    #                 print('-'*80 + '\n' + str(poststate) + '\n' + '-'*80)
    #                 if precondition is None:
    #                     states.append(prestate)
    #                 states.append(poststate)
    #                 return False
    #         wp_checked_valid.add(k)
    #         indicators = (
    #             precondition_indicator(precondition),
    #             mp_indicators[mp],
    #         ) + tuple(lit_indicators[i] for i in sorted(s))
    #         # TODO: does this really help?
    #         wp_valid_solver.add(z3.Or(*(z3.Not(x) for x in indicators)))
    #         wp_valid_solver.add(z3.Implies(
    #             precondition_indicator(precondition),
    #             t.translate_expr(mp.to_clause(s))
    #         ))

    #     return True

    # a: List[Expr] = [] # set of clauses such that: init U states |= a /\ wp(a)
    def get_a() -> List[Expr]:
         # set of clauses such that: init U states |= a /\ wp(a)
        return list(mp.to_clause(s) for mp in maps for s in mp.blocked_up)
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
            # assert set(a) == set(get_a()), (a,get_a())
            return states, dedup_equivalent_predicates(solver, get_a())

        n_states = len(states)

        if not valid(mp.to_clause(seed)):
            # the clause is not valid, grow and block it
            current = seed
            for i in sorted(mp.all_n - seed):
                if not valid(mp.to_clause(current | {i})):
                    current.add(i)
            # assert not valid(mp.to_clause(current))
            mp.block_down(current)
            print(f'block_down: {mp.to_clause(current)}')
            # this may have added new (initial) states

        elif not wp_valid(mp, seed):
            # the clause is was valid, but its wp was not. we already learned a new state so now its not even valid
            # grow the clause (while learning new sates)
            assert len(states) > n_states
            current = seed
            for i in sorted(mp.all_n - seed):
                cl = mp.to_clause(current | {i})
                if not (valid(cl) and wp_valid(mp, current | {i})):
                    current.add(i)
            # assert not valid(mp.to_clause(current))
            mp.block_down(current)
            print(f'block_down: {mp.to_clause(current)}')
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
                if valid(cl) and wp_valid(mp, current - {i}):
                    current.remove(i)
                else:
                    # we don't really want to learn any new states when shrinking, so discard what we found
                    states = states[:n_states]
            print(f'to {len(current)}')
            cl = mp.to_clause(current)
            # assert valid(cl) and wp_valid(cl)
            assert len(states) == n_states
            # a.append(cl)
            mp.block_up(current)
            print(f'block_up: {cl}')

        # maintain a and the solver in case we added new states
        if len(states) > n_states:
             # TODO: do something smarter
            # assert set(a) == set(get_a())
            # a = []
            print(f'forward_explore_marco a was {sum(len(mp.blocked_up) for mp in maps)} predicates, resetting')
            nd = 0
            nu = 0
            for mp in maps:
                down = mp.blocked_down
                up = []
                for s in mp.blocked_up:
                    _states = states
                    states = states[n_states:]
                    if valid(mp.to_clause(s)) and wp_valid(mp, s):
                        up.append(s)
                    states = _states # TODO: we are throwing away states here, need something better, sor of forward_explore_predicates
                mp.reset_solver(up=up, down=down)
                nd += len(down)
                nu += len(up)
            print(f'forward_explore_marco kept {nd} blockings down and {nu} blockings up')
            a = get_a()
    assert False


def forward_explore(s: Solver,
                    alpha: Callable[[Iterable[State]], Sequence[Expr]],
                    states: Optional[Iterable[State]] = None
) -> Tuple[Sequence[State], Sequence[Expr]]:

    if states is None:
        states = []
    else:
        states = list(states)
    a = alpha(states)
    prog = syntax.the_program
    inits = tuple(init.expr for init in prog.inits())

    changes = True
    while changes:
        changes = False

        # check for initial states violating a
        print(f'a is ({len(a)} predicates):' if len(a) > 0 else 'a is true')
        for e in a:
            print(f'  {e}')
        print(f'Checking if init implies everything ({len(a)} predicates)... ', end='')

        m = None
        for p in a:
            m = check_initial(s, p)
            if m is not None:
                break

        if m is not None:
            print('NO')
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
                s,
                inits if precondition is None else precondition,
                p
            )
            # print(res)
            if res is not None:
                _, m = res
                states.append(m)
                changes = True
                a = alpha(states)
                break

    # here init U states |= a, post(init U states) |= a
    # here init U states |= a /\ wp(a)

    #print(states)
    #print(a)
    return states, a


def forward_explore_inv(s: Solver) -> None:
    prog = syntax.the_program
    global cache_path
    cache_path = Path(utils.args.filename).with_suffix('.cache')
    load_caches()
    invs = [inv.expr for inv in prog.invs()] # see examples/lockserv_cnf.pyv
    # invs = list(chain(*(as_clauses(inv.expr) for inv in prog.invs())))
    print('Performing forward explore w.r.t. the following clauses:')
    for p in sorted(invs, key=lambda x: len(str(x))):
        print(p)
    print('='*80)
    def alpha_inv(states: Iterable[State]) -> Sequence[Expr]:
        return sorted(
            dedup_equivalent_predicates(s, chain(*(alpha_from_clause(s, states, clause) for clause in invs))),
            key=lambda x: (len(str(x)),str(x))
        )
    states, a = forward_explore(s, alpha_inv)
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
    dump_caches()


def dedup_equivalent_predicates(s: Solver, itr: Iterable[Expr]) -> Sequence[Expr]:
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


def repeated_houdini(s: Solver) -> str:
    '''The (proof side) repeated Houdini algorith, either sharp or not.
    '''
    prog = syntax.the_program
    global cache_path
    cache_path = Path(utils.args.filename).with_suffix('.cache')
    load_caches()

    sharp = utils.args.sharp
    safety = tuple(inv.expr for inv in prog.invs() if inv.is_safety)
    reachable_states : Sequence[State] = ()
    clauses : List[Expr] = list(chain(*(as_clauses(x) for x in safety)))  # all top clauses in our abstraction
    sharp_predicates : Sequence[Expr] = ()  # the sharp predicates (minimal clauses true on the known reachable states)
    def alpha_clauses(states: Iterable[State]) -> Sequence[Expr]:
        return sorted(
            dedup_equivalent_predicates(s, chain(*(alpha_from_clause(s, states, clause) for clause in clauses))),
            key=lambda x: (len(str(x)),str(x))
        )
    def alpha_sharp(states: Iterable[State]) -> Sequence[Expr]:
        return sorted(
            alpha_from_predicates(s, states, sharp_predicates),
            key=lambda x: (len(str(x)),str(x))
        )
    while True:
        # reachable_states, a = forward_explore(s, alpha_clauses, reachable_states)
        reachable_states, a = forward_explore_marco(s, clauses, reachable_states)
        print(f'Current reachable states ({len(reachable_states)}):')
        for m in reachable_states:
            print(str(m) + '\n' + '-'*80)
        if check_implication(s, a, safety) is not None:
            print('Found safety violation!')
            dump_caches()
            return 'UNSAFE'
        sharp_predicates = tuple(a)
        print(f'Current sharp predicates ({len(sharp_predicates)}):')
        for p in sharp_predicates:
            print(p)
        states = reachable_states
        unreachable = []
        while True:
            for p in a:
                res = check_two_state_implication(s, a, p, 'CTI')
                if res is not None:
                    prestate, poststate = res
                    unreachable.append(prestate)
                    states, a = forward_explore(
                        s,
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
            dump_caches()
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
            assert clauses == list(dedup_equivalent_predicates(s, clauses))
            print('='*80)

NatInf = Optional[int] # None represents infinity
Point = Tuple[Union[FrozenSet[int],NatInf],...]
Constraint = Union[Dict[int,bool],int]
# a constraint for a set some elements to be there or not, and a constraint for NatInf is an upper bound
class MonotoneFunction(object):
    '''This class represents information about a monotone function to
    {0,1}. The domain of the function is D_1 x ... x D_n, where each
    D_i is either the powerset domain of some (finite or countably
    infinite) set, or NatInf. In each of its arguments, the function
    can either be monotonically increasing ('+') or decreasing
    ('-'). For powerset domain, the function can also be disjunctive
    ('|') or conjunctive ('&'), meaning that it disributes over union,
    so it is actually determined by its values for singleton sets
    (naturally, disjunctive is increasing, conjunctive is decreasing,
    and for the empty set the are 0 and 1 respectively.)

    An instance represents partial knowledge of the actual monotone
    function, encoded by some (possibly maximal) points where it is
    known to evaluate to 0, and some (possibly minimal) points where
    it is known to be 1. This partial knowledge is formally a partial
    monotone function.

    The class supports the following interface:

    query(x_1,...,x_n) -> Optional[bool]: evaluates the partial function

    learn(x_1,...,x_n,v) -> None: add more information

    seed(C_1,...,C_n) -> Optional[Tuple[D_1,...,D_n]]: each C_i is a
    constraint, which represents a subset of D_i (e.g., instead of the
    full powerset, a powerset contained in some finite set and
    contains some other set, or instead of NatInf some finite set of
    possible numbers). The result is either None, meaning the partial
    function is total on C_1 x ... x C_n, or an element of C_1 x ... x
    C_n for which the partial function is underfined.

    seed supports several biasing modes, causing it to procedure lower
    or higher seeds, with varying levels of strictness.

    '''
    def __init__(self, dms: Sequence[Tuple[Optional[List], str]]):
        # None represents NatInf, List represents powerset domain of
        # list elements. The passed list can be extended, but
        # otherwise should not be modified
        for d, m in dms:
            assert m in ('+', '-', '|', '&'), f'Illegal monotonicity: {m!r}'
        self.n = len(dms)
        self.domains = tuple(d for d, m in dms)
        self.directions = tuple(m for d, m in dms)
        self.zeros: List[Point] = []
        self.ones: List[Point] = []

    def assert_points(self, *points: Point) -> None:
        # assert points are well typed points
        for xs in points:
            assert isinstance(xs, tuple)
            assert len(xs) == self.n
            for x, d in zip(xs, self.domains):
                if d is None:
                    assert (x is None) or (isinstance(x, int) and 0 <= x), f'Bad value {x!r} for domain NatInf'
                else:
                     assert isinstance(x, frozenset) and all(
                         isinstance(i, int) and 0 <= i < len(d)
                         for i in x
                     ), f'Bad value {x!r} for domain list of length {len(d)}'

    def leq(self, xs: Point, ys: Point) -> bool:
        self.assert_points(xs, ys)
        return all(
            xx <= yy if m in ('+', '|') else yy <= xx  # type: ignore
            for x, y, m in zip(xs, ys, self.directions)
            for xx in [x if x is not None else math.inf]
            for yy in [y if y is not None else math.inf]
        )

    def __getitem__(self, xs: Point) -> Optional[bool]:
        self.assert_points(xs)
        if any(xs <= ys for ys in self.zeros):
            return False
        elif any(ys <= xs for ys in self.ones):
            return True
        else:
            return None

    def __setitem__(self, xs: Point, v: bool) -> None:
        self.assert_points(xs)
        assert self[xs] is None
        if v:
            self.ones.append(xs)
        else:
            self.zeros.append(xs)
        # TODO: maybe remove some reduntetd points
        # TODO: maybe store wethat or not the point is min/max

    def seed(self, constraints: Sequence[Constraint]) -> Optional[Point]:
        assert len(constraints) == self.n
        assert all(
            isinstance(c, int) if d is None else
            isinstance(c, dict)
            for c, d in zip(constraints, self.domains)
        )
        # TODO: for now we use a fresh z3 solver every time, but this should be made incremental
        solver = z3.Solver()
        vss: List[Union[List[z3.ExprRef], z3.ExprRef]] = [
            [z3.Bool(f'{i}_{j}') for j in range(len(d))] if d is not None else
            z3.Int(f'{i}')
            for i, d in enumerate(self.domains)
        ]

        for c, d, vs in zip(constraints, self.domains, vss):
            if isinstance(c, int):
                assert d is None
                assert isinstance(vs, z3.ExprRef)
                solver.add(vs < c)  # type: ignore
                # TODO: fix the stup of z3 to support this
            else:
                assert isinstance(d, list)
                assert isinstance(vs, list)
                for i, v in c.items():
                    assert 0 <= i < len(d)
                    solver.add(vs[i] if v else z3.Not(vs[i]))

        # block down from the zero points
        for xs, v in chain(zip(self.zeros,repeat(False)), zip(self.ones,repeat(True))):
            lits: List[z3.ExprRef] = []
            for x, vs, d, m in zip(xs, vss, self.domains, self.directions):
                if d is None:
                    # TODO: get this right
                    continue
                    assert (x is None) or (isinstance(x, int) and 0 <= x)
                    assert isinstance(vs, z3.ExprRef)
                    assert m in ('+', '-')
                    if x is None and m == '+':
                        pass
                    elif x is None and m == '-':
                        pass # TODO: not really sure, need to think of the encoding of Inf in z3
                else:
                    assert isinstance(x, frozenset) and all(
                        isinstance(i, int) and 0 <= i < len(d)
                        for i in x
                    ), f'Bad value {x!r} for domain list of length {len(d)}'
                    assert isinstance(vs, list)
                    assert m in ('+', '|', '-', '&')
                    if v != (m in ('+', '|')):
                        # "block down"
                        lits.extend(vs[i] for i in range(len(d)) if i not in x)
                    else:
                        # "block up"
                        lits.extend(z3.Not(vs[i]) for i in range(len(d)) if i in x)
            solver.add(z3.Or(*lits))

        res = solver.check()
        assert res in (z3.unsat, z3.sat)
        if res == z3.unsat:
            return None
        else:
            model = solver.model()
            # default to "low bias" (small sets for +, large sets for -) TODO: make the bias more flexible
            result: Point = ()
            for vs, d, m in zip(vss, self.domains, self.directions):
                if d is None:
                    assert isinstance(vs, z3.ExprRef)
                    k = model[vs]
                    if k is None:
                        # k undefined in the model, default to 0
                        result += (0,)
                    else:
                        assert isinstance(k, z3.z3.IntNumRef)  # type: ignore # TODO
                        result += (k.as_long(),)
                else:
                    assert isinstance(vs, list)
                    assert m in ('+', '|', '-', '&')
                    if (m in ('+', '|')):
                        # bias to small set
                        result += (frozenset(
                            i
                            for i in range(len(d))
                            if z3.is_true(model[vs[i]])
                        ),)
                    else:
                        # bias to large set
                        (frozenset(
                            i
                            for i in range(len(d))
                            if not z3.is_false(model[vs[i]])
                        ),)
            return result

    def to_elems(self, xs: Point) -> Tuple:
        self.assert_points(xs)
        result: Tuple = ()
        for x, d in zip(xs, self.domains):
            if d is None:
                assert x is None or isinstance(x, int)
                result += (x,)
            else:
                assert isinstance(x, frozenset)
                result += ([e for i,e in enumerate(d) if i in x],)
        return result



def add_argparsers(subparsers: argparse._SubParsersAction) -> Iterable[argparse.ArgumentParser]:
    result : List[argparse.ArgumentParser] = []

    # forward_explore_inv
    s = subparsers.add_parser('pd-forward-explore-inv', help='Forward explore program w.r.t. its invariant')
    s.set_defaults(main=forward_explore_inv)
    result.append(s)

    # repeated_houdini
    s = subparsers.add_parser('pd-repeated-houdini', help='Run the repeated Houdini algorith in the proof space')
    s.set_defaults(main=repeated_houdini)
    s.add_argument('--sharp', action=utils.YesNoAction, default=True,
                   help='search for sharp invariants')

    result.append(s)

    return result
