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

from typing import TypeVar, Iterable, FrozenSet, Union, Callable, Generator, Set, Optional, cast, Type, Collection

A = TypeVar('A')
# form: https://docs.python.org/3/library/itertools.html#itertools-recipes
def powerset(iterable: Iterable[A]) -> Iterator[Tuple[A, ...]]:
    'powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)'
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))


State = Model
Predicate = Expr


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
_solver: Optional[Solver] = None
def eval_in_state(s: Optional[Solver], m: State, p: Expr) -> bool:
    global _solver
    if s is None:
        if _solver is None:
            _solver = Solver()
        s = _solver
    cache = _cache_eval_in_state
    k = (m, p)
    if k not in cache:
        if m.z3model is not None:
            try:
                cache[k] = eval_quant(m.z3model, s.get_translator(m.keys[0]).translate_expr(p))
            except:
                print(m)
                raise
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
                    assert False, 'Probably because state isomorphism is not handled correctly yet...'
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


def check_k_state_implication(
        s: Solver,
        precondition: Union[Iterable[Expr], State],
        p: Expr,
        k: int,
        msg: str = 'transition',
) -> Optional[Tuple[State,...]]:
    # TODO: we should cache these

    if not isinstance(precondition, State):
        precondition = tuple(precondition)

    om = check_bmc(
        s,
        p,
        k,
        [precondition.as_onestate_formula(0)] if isinstance(precondition, State) else precondition,
    )
    if om is None:
        return None
    else:
        z3m = om.z3model
        assert z3m is not None
        keys = list(om.keys)
        states = tuple(
            Model.from_z3(keys[i:], z3m)
            for i in reversed(range(len(keys)))
        )
        print(f'Found new {k}-{msg} violating {p}:')
        print('-'*80 + '\n' + str(states[-1]) + '\n' + '-'*80)
        return states


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
                    alpha: Callable[[Collection[State]], Sequence[Expr]],
                    states: Optional[Iterable[State]] = None
) -> Tuple[List[State], Sequence[Expr], List[int], List[Tuple[int, int]]]:
    '''
    forward exploration from given states
    result is: more_states, a, initial, transitions
    more_states is an extension of states
    a is the abstract value of more_states
    initial are indicies to more_states of initial states
    transitions are indicies to more_states of transitions
    '''
    # TODO: make cleanup pass and reduce printing (added when adding BMC unrolling)
    res: Optional[Tuple[State,...]] = None

    if states is None:
        states = []
    else:
        states = list(states)
    a = alpha(states)
    prog = syntax.the_program
    inits = tuple(init.expr for init in prog.inits())
    initial: List[int] = []
    transitions: List[Tuple[int, int]] = []

    changes = True
    while changes:
        changes = False

        # check for initial states violating a
        # print(f'have {len(states)} states')
        # print(f'a is ({len(a)} predicates):' if len(a) > 0 else 'a is true')
        # for e in a:
        #     print(f'  {e}')
        # print(f'Checking if init implies everything ({len(a)} predicates)... ', end='')

        m = None
        for p in a:
            m = check_initial(s, p)
            if m is not None:
                break
        if m is not None:
            initial.append(len(states))
            states.append(m)
            changes = True
            a = alpha(states)
            continue
        else:
            # print('YES')
            pass

        m = None
        # check for 1 transition from an initial state or a state in states
        preconditions = chain(
            (s for s in states if len(s.keys) == 1), # discovered initial states
            [None], # general initial state
            (s for s in states if len(s.keys) > 1) # discovered non-initial states
        )
        label = lambda s: 'init' if s is None else 'initial state' if len(s.keys) == 1 else 'state'
        for precondition, p in product(preconditions, a):
            # print(f'Checking if {label(precondition)} satisfies WP of {p}... ',end='')
            res = check_two_state_implication(
                s,
                inits if precondition is None else precondition,
                p,
            )
            if res is not None:
                prestate, poststate = res
                if precondition is None:
                    # add new initial state
                    initial.append(len(states))
                    states.append(prestate)
                    precondition = prestate
                transitions.append((states.index(precondition), len(states)))
                states.append(poststate)
                changes = True
                a = alpha(states)
                break
            else:
                # print('YES')
                pass
        if m is not None:
            continue

        if utils.args.unroll_to_depth is None:
            continue

        # check for k-transition from an initial state or a state in states
        preconditions = chain(
            (s for s in states if len(s.keys) == 1), # discovered initial states
            [None], # general initial state
            (s for s in states if len(s.keys) > 1) # discovered non-initial states
        )
        for k, precondition, p in product(range(2, utils.args.unroll_to_depth + 1), preconditions, a):
            print(f'Checking if {label(precondition)} satisfies WP_{k} of {p}... ',end='')
            res = check_k_state_implication(
                s,
                inits if precondition is None else precondition,
                p,
                k,
            )
            if res is not None:
                prestate, *poststates = res
                # add all states, including first one if it's a new initial state
                if precondition is None:
                    # add new initial state
                    initial.append(len(states))
                    states.append(prestate)
                    precondition = prestate
                i = states.index(precondition)
                for poststate in poststates:
                    transitions.append((i, len(states)))
                    i = len(states)
                    states.append(poststate)
                changes = True
                a = alpha(states)
                break
            else:
                print('YES')

    # here init U states |= a, post^k(init U states) |= a
    # here init U states |= a /\ wp^k(a)

    #print(states)
    #print(a)
    return states, a, initial, transitions


def forward_explore_inv(s: Solver) -> None:
    prog = syntax.the_program
    global cache_path
    cache_path = Path(utils.args.filename).with_suffix('.cache')
    load_caches()
    # invs = [inv.expr for inv in prog.invs()] # see examples/lockserv_cnf.pyv
    invs = list(chain(*(as_clauses(inv.expr) for inv in prog.invs())))
    print('Performing forward explore w.r.t. the following clauses:')
    for p in sorted(invs, key=lambda x: len(str(x))):
        print(p)
    print('='*80)
    def alpha_inv(states: Iterable[State]) -> Sequence[Expr]:
        return sorted(
            dedup_equivalent_predicates(s, chain(*(alpha_from_clause(s, states, clause) for clause in invs))),
            key=lambda x: (len(str(x)),str(x))
        )
    states, a, _, _ = forward_explore(s, alpha_inv)
    len(states)
    print('Done!\n' + '='*80)
    print('The resulting invariant after forward exporation (V/X - inductive or not):')
    for p in sorted(a, key=lambda x: len(str(x))):
        print(
            ('  V  ' if check_two_state_implication_all_transitions(s, a, p) is None else '  X  ') +
            str(p)
        )
    print('='*80)
    print(f'Found {len(states)} states and transitions:\n' + '-'*80)
    for x in states:
        print(x)
        print('-'*80)
    dump_caches()


def dedup_equivalent_predicates(s: Solver, itr: Iterable[Expr]) -> Sequence[Expr]:
    ps = list(itr)
    print(f'Deduping {len(ps)} predicates to...',end=' ')
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

    # TODO: get this from command line option, and from the right file
    # with open('reachable-states.cache', 'rb') as cache_file:
    #     reachable_states = tuple(pickle.load(cache_file))
    # print('initialized reachable states:')
    # for m in reachable_states:
    #     print(str(m) + '\n' + '-'*80)

    clauses : List[Expr] = list(chain(*(as_clauses(x) for x in safety)))  # all top clauses in our abstraction
    sharp_predicates : Sequence[Expr] = ()  # the sharp predicates (minimal clauses true on the known reachable states)
    def alpha_clauses(states: Collection[State]) -> Sequence[Expr]:
        return sorted(
            dedup_equivalent_predicates(s, chain(*(alpha_from_clause(s, states, clause) for clause in clauses))),
            key=lambda x: (len(str(x)),str(x))
        )
    def alpha_sharp(states: Collection[State]) -> Sequence[Expr]:
        return sorted(
            alpha_from_predicates(s, states, sharp_predicates),
            key=lambda x: (len(str(x)),str(x))
        )
    while True:
        # reachable_states, a, _, _ = forward_explore(s, alpha_clauses, reachable_states)
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
                    states, a, _, _ = forward_explore(
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
# TODO: maybe these should be classes with their own methds
Point = Tuple[Union[FrozenSet[int],NatInf],...]
Constraint = Union[
    Dict[int,bool], # constraint for a set forcing some elements to be in or out
    Tuple[Optional[int],Optional[int]], # constraint for NatInf, range
    None, # no constraint
]
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
        if any(self.leq(xs, ys) for ys in self.zeros):
            return False
        elif any(self.leq(ys, xs) for ys in self.ones):
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
        # TODO: maybe store whether or not the point is min/max

    def seed(self, constraints: Sequence[Constraint]) -> Optional[Point]:
        # TODO: support configurable biases
        assert len(constraints) == self.n
        assert all(
            (c is None) or
            (isinstance(c, tuple) and d is None) or
            (isinstance(c, dict) and isinstance(d, list))
            for c, d in zip(constraints, self.domains)
        )
        # TODO: for now we use a fresh z3 solver every time, but this should be made incremental
        solver = z3.Solver()
        vss: List[Union[List[z3.ExprRef], z3.ExprRef]] = [
            [z3.Bool(f'x_{i}_{j}') for j in range(len(d))] if d is not None else
            z3.Int(f'k_{i}')
            for i, d in enumerate(self.domains)
        ]

        # add non-negativity constraints
        for d, vs in zip(self.domains, vss):
            if d is None:
                solver.add(vs >= 0)  # type: ignore

        # add constraints
        for c, d, vs in zip(constraints, self.domains, vss):
            if c is None:
                continue
            elif isinstance(c, tuple):
                assert d is None
                assert isinstance(vs, z3.ExprRef)
                lo, hi = c
                if lo is not None:
                    solver.add(lo <= vs)  # type: ignore
                if hi is not None:
                    solver.add(vs < hi)  # type: ignore
                # TODO: fix the stub of z3 to support the above
            else:
                assert isinstance(d, list)
                assert isinstance(vs, list)
                for i, v in c.items():
                    assert 0 <= i < len(d)
                    solver.add(vs[i] if v else z3.Not(vs[i]))
        # print(f'Solver after constraints: {solver}')

        # block according to self.zeros and self.ones
        for xs, v in chain(zip(self.zeros,repeat(False)), zip(self.ones,repeat(True))):
            lits: List[z3.ExprRef] = []
            for x, vs, d, m in zip(xs, vss, self.domains, self.directions):
                if d is None:
                    assert (x is None) or (isinstance(x, int) and 0 <= x)
                    assert isinstance(vs, z3.ExprRef)
                    if v != (m == '+'):
                        # "block down"
                        if x is not None:
                            lits.append(vs > x)  # type: ignore
                        else:
                            # nothing larger than infinity
                            pass
                    else:
                        # "block up"
                        if x is not None:
                            lits.append(vs < x)  # type: ignore
                        else:
                             # anything is smaller than infinity (we
                             # never return infinity in seeds)
                            lits.append(z3.BoolVal(True))
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
            solver.add(z3.Or(*lits) if len(lits) > 0 else z3.BoolVal(False))
        # print(f'Solver after blocking: {solver}')

        res = solver.check()
        # print(f'solver.check() = {res}')
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
                        assert isinstance(k, z3.IntNumRef)  # type: ignore # TODO
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
                        result += (frozenset(
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
                assert isinstance(x, frozenset) and all(0 <= i < len(d) for i in x)
                result += ([e for i,e in enumerate(d) if i in x],)
        return result

# The following 3 commented out functions are a very basic and naive
# implementation of "cdcl_invariant" that does not really work well,
# but it can be run
#
# def separate(solver: Solver, A: Sequence[State], B: Sequence[State], k: int) -> Optional[Sequence[Predicate]]:
#     '''
#     Find a conjunction of at most k universally quantified clauses
#     that are positive on all of the A states, and eliminate all of the
#     B states, or return None if that's impossible.
#     '''
#     # for now, a naive implementation that eagerly finds all the
#     # minimal subclauses of the negations of diagrams of B that are
#     # true on A, and then does set cover using z3.
#     top_clauses: List[Predicate] = []
#     for s in B:
#         cs = as_clauses(Not(s.as_diagram(0).to_ast()))
#         assert len(cs) == 1
#         c = cs[0]
#         if c not in top_clauses:
#             top_clauses.append(c)
#     predicates = sorted(
#         dedup_equivalent_predicates(solver, chain(*(alpha_from_clause(solver, A, clause) for clause in top_clauses))),
#         key=lambda x: (len(str(x)),str(x))
#     )
#     print(f'Separating using the following {len(predicates)} predicates:')
#     for c in predicates:
#         print(f'  {c}')
#     covers = [
#         set(i for i, s in enumerate(B) if not eval_in_state(solver, s, p))
#         for p in predicates
#     ]
#     print(f'The set cover problem is: {covers}')
#     vs = [z3.Bool(f'p{i}') for i, p in enumerate(predicates)]
#     z3s = z3.Solver()
#     for i, t in enumerate(B):
#         z3s.add(z3.Or(*(
#             vs[j] for j in range(len(predicates))
#             if i in covers[j]
#         )))
#     if len(vs) > k:
#         z3s.add(z3.AtMost(*vs, k))  # type: ignore # TODO fix this typing issue
#     res = z3s.check()
#     assert res in (z3.unsat, z3.sat)
#     if res == z3.unsat:
#         return None
#     else:
#         model = z3s.model()
#         return [p for p, v in zip(predicates,vs) if z3.is_true(model[v])]


# def find_invariant(solver: Solver,
#                    states: Sequence[State],
#                    reachable: Sequence[int], # indices into states
#                    bad: Sequence[int], # indices into states
#                    transitions: Sequence[Tuple[int, int]], # indices into states
#                    k: int) -> Optional[Sequence[Predicate]]:
#     '''Find an inductive invariant with at most k predicates that is
#     positive on reachable, negative on bad, and respects transitions
#     '''
#     z3s = z3.Solver()
#     vs = [z3.Bool(f's_{i}') for i in range(len(states))] # s_i encodes that the invariant is satisfied by state i
#     for i in reachable:
#         z3s.add(vs[i])
#     for i in bad:
#         z3s.add(z3.Not(vs[i]))
#     for i,j in transitions:
#         z3s.add(z3.Implies(vs[i], vs[j]))
#     while True:
#         res = z3s.check()
#         assert res in (z3.unsat, z3.sat)
#         if res == z3.unsat:
#             # no invariant with less than k predicates
#             return None
#         else:
#             model = z3s.model()
#             A = [s for s, v in zip(states, vs) if z3.is_true(model[v])]
#             B = [s for s, v in zip(states, vs) if z3.is_false(model[v])]
#             inv = separate(solver, A, B, k)
#             if inv is None:
#                 # learn an unseparability conflict clause TODO: minimize it
#                 z3s.add(z3.Or(*chain(
#                     (z3.Not(v) for v in vs if z3.is_true(model[v])),
#                     (v for v in vs if z3.is_false(model[v])),
#                 )))
#             else:
#                 # found invariant
#                 return inv

# def cdcl_invariant(solver:Solver) -> str:
#     prog = syntax.the_program
#     global cache_path
#     cache_path = Path(utils.args.filename).with_suffix('.cache')
#     load_caches()

#     safety = tuple(inv.expr for inv in prog.invs() if inv.is_safety)

#     states : List[State] = []
#     reachable: List[int] = []
#     bad: List[int] = []
#     transitions: List[Tuple[int, int]] = []

#     k = 0
#     while True:
#         print(f'Current reachable states ({len(reachable)}):')
#         for i in reachable:
#             print(str(states[i]) + '\n' + '-'*80)
#             if check_implication(solver, [states[i].as_onestate_formula(0)], safety) is not None:
#                 print('Found safety violation!')
#                 dump_caches()
#                 return 'UNSAFE'
#         inv = find_invariant(solver, states, reachable, bad, transitions, k)
#         if inv is None:
#             print(f'No invariant with {k} predicates, increasing bound\n\n')
#             k += 1
#             continue
#         inv = list(chain(safety, inv))
#         print(f'Candidate inductive invariant ({len(inv)} predicates) is:' if len(inv) > 0 else 'Candidate inductive invariant is true')
#         for p in sorted(inv, key=lambda x: len(str(x))):
#             print(f'  {p}')
#         for p in inv:
#             s = check_initial(solver, p)
#             if s is not None:
#                 states.append(s)
#                 reachable.append(len(states) - 1)
#                 break
#         else:
#             for i, p in enumerate(inv):
#                 res = check_two_state_implication(solver, inv, p, 'CTI')
#                 if res is not None:
#                     prestate, poststate = res
#                     states.append(prestate)
#                     states.append(poststate)
#                     transitions.append((len(states) - 2, len(states) - 1))
#                     if i < len(safety):
#                         assert p == safety[i]
#                         bad.append(len(states) - 1)
#                     break
#             else:
#                 print('Inductive invariant foundlies safety!')
#                 dump_caches()
#                 return 'SAFE'

def destruct_clause(clause: Expr) -> Tuple[Tuple[SortedVar,...], Tuple[Expr,...]]:
    '''
    clause is either FalseExpr, or universally quantifier or quantifier free, and the body is either a disjunction or a single literal. returns (variables, literals).
    '''
    if clause == FalseExpr:
        return (), ()
    if isinstance(clause, QuantifierExpr):
        body = clause.body
        variables = tuple(clause.binder.vs)
    else:
        body = clause
        variables = ()
    if isinstance(body, NaryExpr):
        assert body.op == 'OR', clause
        literals = tuple(body.args)
    else:
        assert isinstance(body, (Id, UnaryExpr, Bool, AppExpr, BinaryExpr)), f'{clause}\n{isinstance(clause, QuantifierExpr)}\n{body}\n{type(body)}'
        literals = (body, )
    assert len(set(literals)) == len(literals)
    return variables, literals


def is_strict_subclause(c1: Expr, c2: Expr) -> bool:
    if c2 == FalseExpr:
        return False
    if c1 == FalseExpr:
        return True
    _, lits1 = destruct_clause(c1)
    _, lits2 = destruct_clause(c2)
    return set(lits1) < set(lits2)


def minimize_clause(p: Expr, states: Sequence[State]) -> Expr:
    '''
    p is a clause, try to find a smaller clause satisfied by all states
    '''
    if p == FalseExpr:
        return p
    variables, literals = destruct_clause(p)
    n = len(literals)

    def to_clause(s: Set[int]) -> Expr:
        lits = [literals[i] for i in s]
        free = set(chain(*(lit.free_ids() for lit in lits)))
        vs = [v for v in variables if v.name in free]
        return Forall(vs, Or(*lits)) if len(vs) > 0 else Or(*lits)

    def f(s: Set[int]) -> bool:
        clause = to_clause(s)
        return all(eval_in_state(None, m, clause) for m in states)

    current = set(range(n))
    assert f(current)
    for i in range(n):
        if i in current and f(current - {i}):
            current.remove(i)
    assert len(current) <= n
    if len(current) == n:
        return p
    else:
        return to_clause(current)


class SeparabilitySubclausesMap(object):
    '''
    Class used to store a map of subclauses of a certain clause, and
    obtain subclauses that are positive and negative on some given
    states.
    '''
    def __init__(self,
                 top_clause: Expr,
                 states: List[State],  # assumed to only grow
                 predicates: List[Expr],  # assumed to only grow
    ):
        '''
        states is assumed to be a list that is increasing but never modified
        '''
        self.states = states
        self.predicates = predicates
        self.variables, self.literals = destruct_clause(top_clause)
        self.n = len(self.literals)
        self.all_n = set(range(self.n))  # used in complement fairly frequently
        self.solver = z3.Solver()
        self.lit_vs = [z3.Bool(f'lit_{i}') for i, _ in enumerate(self.literals)]
        self.state_vs: List[z3.ExprRef] = []
        self.predicate_vs: List[z3.ExprRef] = []
        self._new_states()
        self._new_predicates()

    def _new_states(self) -> None:
        self.state_vs.extend(z3.Bool(f's_{i}') for i in range(len(self.state_vs), len(self.states)))

    def _new_predicates(self) -> None:
        new = range(len(self.predicate_vs), len(self.predicates))
        self.predicate_vs.extend(z3.Bool(f'p_{i}') for i in new)
        for i in new:
            _, literals = destruct_clause(self.predicates[i])
            lits = set(literals)
            if lits <= set(self.literals):
                # we need to block up from strict supersets of literals
                # TODO: should this be strict or not?
                x = ([z3.Not(self.predicate_vs[i])] +
                     [z3.Not(self.lit_vs[j]) for j in range(self.n) if self.literals[j] in lits]
                )
                for j in range(self.n):
                    if self.literals[j] not in lits:
                        self.solver.add(z3.Or(*x, z3.Not(self.lit_vs[j])))

    def separate(self,
                 pos: Collection[int],
                 neg: Collection[int],
                 sharp: Collection[int],
    ) -> Optional[FrozenSet[int]]:
        '''
        find a subclause that is positive on pos and negative on neg. pos,neg are indices to self.states.

        TODO: to we need an unsat core in case there is no subclause?
        '''
        self._new_states()
        self._new_predicates()
        assert all(0 <= i < len(self.states) for i in chain(pos, neg))
        assert all(0 <= i < len(self.predicates) for i in sharp)
        sep = list(chain(
            (self.state_vs[i] for i in sorted(pos)),
            (z3.Not(self.state_vs[i]) for i in sorted(neg)),
            (self.predicate_vs[i] for i in sorted(sharp)),
        ))
        while True:
            res = self.solver.check(*sep)
            assert res in (z3.unsat, z3.sat)
            if res == z3.unsat:
                return None
            # minimize for strongest possible clause
            model = self.solver.model()
            forced_to_false = set(
                i for i, v in enumerate(self.lit_vs)
                if not z3.is_true(model[v])
            )
            for i, _ in enumerate(self.lit_vs):
                if i in forced_to_false:
                    continue
                res = self.solver.check(*sep, *(z3.Not(self.lit_vs[j]) for j in sorted(chain(forced_to_false, [i]))))
                assert res in (z3.unsat, z3.sat)
                if res == z3.sat:
                    forced_to_false.add(i)
            assert self.solver.check(*sep, *(z3.Not(self.lit_vs[j]) for j in sorted(forced_to_false))) == z3.sat
            result = frozenset(self.all_n - forced_to_false)
            clause = self.to_clause(result)
            # now check if this clause does the job w.r.t. pos and neg
            bad = False
            for i in pos:
                if not eval_in_state(None, self.states[i], clause):
                    # grow and block down
                    current = result
                    for j in sorted(self.all_n - result):
                        if not eval_in_state(None, self.states[i], self.to_clause(current | {j})):
                            current = current | {j}
                    self.solver.add(z3.Or(z3.Not(self.state_vs[i]), *(
                        self.lit_vs[j] for j in sorted(self.all_n - current)
                    )))
                    bad = True
                    break # TODO: should we be eager or lazy here?
            if bad:
                continue # TODO: should we be eager or lazy here?
            for i in neg:
                if eval_in_state(None, self.states[i], clause):
                    # shrink and block up
                    current = result
                    for j in sorted(result):
                        if eval_in_state(None, self.states[i], self.to_clause(current - {j})):
                            current = current - {j}
                    self.solver.add(z3.Or(self.state_vs[i], *(
                        z3.Not(self.lit_vs[j]) for j in sorted(current)
                    )))
                    bad = True
                    break # TODO: should we be eager or lazy here?
            if bad:
                continue
            return result

    def to_clause(self, s: Iterable[int]) -> Expr:
        lits = [self.literals[i] for i in sorted(s)]
        free = set(chain(*(lit.free_ids() for lit in lits)))
        vs = [v for v in self.variables if v.name in free]
        return Forall(vs, Or(*lits)) if len(vs) > 0 else Or(*lits)


class SeparabilityMap(object):
    '''
    Marco map for function sep: 2^states x 2^states -> {0,1}
    0 means they can be separated, 1 means they cannot.
    '''
    def __init__(self,
                 states: List[State],  # assumed to only grow
                 predicates: List[Expr],  # assumed to only grow
    ):
        self.states = states
        self.predicates = predicates
        self.maps: List[SeparabilitySubclausesMap] = []
        # self.solver = z3.Solver()
        # self.pos: List[z3.ExprRef] = []
        # self.neg: List[z3.ExprRef] = []
        self.separable: List[Tuple[FrozenSet[int], FrozenSet[int], FrozenSet[int], Predicate]] = []
        self.inseparable: List[Tuple[FrozenSet[int], FrozenSet[int], FrozenSet[int]]] = []
        self._n_predicates = 0
        self._new_states()
        self._new_predicates()

    def _new_states(self) -> None:
        # for i in range(len(self.pos), len(self.states)):
        #     self.pos.append(z3.Bool(f'pos_{i}'))
        #     self.neg.append(z3.Bool(f'neg_{i}'))
        #     self.solver.add(z3.Or(z3.Not(self.pos[i]), z3.Not(self.neg[i])))

        # create new SeparabilitySubclausesMap's
        for i in range(len(self.maps), len(self.states)):
            cs = as_clauses(Not(self.states[i].as_diagram(0).to_ast()))
            assert len(cs) == 1
            c = cs[0]
            self.maps.append(SeparabilitySubclausesMap(c, self.states, self.predicates))

        # update separable with predicate values on new states
        allstates = frozenset(range(len(self.states)))
        for i, (pos, neg, sharp, p) in enumerate(self.separable):
            for j in sorted(allstates - pos - neg):
                if eval_in_state(None, self.states[j], p):
                    pos = pos | {j}
                else:
                    neg = neg | {j}
            self.separable[i] = (pos, neg, sharp, p)

    def _new_predicates(self) -> None:
        # update separable with possibly more sharp predicates
        for i, (pos, neg, sharp, p) in enumerate(self.separable):
            sharp = sharp | frozenset(
                j
                for j in range(self._n_predicates, len(self.predicates))
                if not is_strict_subclause(self.predicates[j], p)
                # TODO: should this be strict or not?
            )
            self.separable[i] = (pos, neg, sharp, p)
        self._n_predicates = len(self.predicates)

    def separate(self,
                 pos: FrozenSet[int],
                 neg: FrozenSet[int],
                 sharp: FrozenSet[int]
    ) -> Union[Predicate, Tuple[FrozenSet[int], FrozenSet[int], FrozenSet[int]]]:
        '''Try to find a predicate positive on pos and negative on neg, and
        sharp on sharp. Either return it, or return subsets of pos,
        neg, sharp that already make it impossible

        '''
        p: Optional[Predicate] = None
        self._new_states()
        self._new_predicates()
        for _pos, _neg, _sharp, p in self.separable:
            if pos <= _pos and neg <= _neg and sharp <= _sharp:
                return p
        for _pos, _neg, _sharp in self.inseparable:
            if _pos <= pos and _neg <= neg and _sharp <= sharp:
                return _pos, _neg, _sharp
        p = self._new_separator(pos, neg, sharp)
        if p is not None:
            # grow is trivial
            pos = frozenset(i for i, s in enumerate(self.states) if eval_in_state(None, s, p))
            neg = frozenset(range(len(self.states))) - pos
            sharp = frozenset(
                i for i in range(len(self.predicates))
                if not is_strict_subclause(self.predicates[i], p)
                # TODO: should this be strict or not?
            )
            print(f'Managed to separate: pos={sorted(pos)}, neg={sorted(neg)}, sharp={sorted(sharp)} with: {p}')
            self.separable.append((pos, neg, sharp, p))
            return p
        else:
            # shrink neg
            for i in sorted(neg):
                if i not in neg:
                    assert False # TODO this can happen once we have "unsat cores" from new_separator
                    continue
                if self._new_separator(pos, neg - {i}, sharp) is None:
                    neg = neg - {i}
            # shrink pos
            for i in sorted(pos):
                if i not in pos:
                    assert False # TODO this can happen once we have "unsat cores" from new_separator
                    continue
                if self._new_separator(pos - {i}, neg, sharp) is None:
                    pos = pos - {i}
            # shrink sharp
            for i in sorted(sharp):
                if i not in sharp:
                    assert False # TODO this can happen once we have "unsat cores" from new_separator
                    continue
                if self._new_separator(pos, neg, sharp - {i}) is None:
                    sharp = sharp - {i}
            self.inseparable.append((pos, neg, sharp))
            return pos, neg, sharp

    def _new_separator(self,
                       pos: FrozenSet[int],
                       neg: FrozenSet[int],
                       sharp: FrozenSet[int]
    ) -> Optional[Predicate]:
        # TODO: this should also give "unsat cores"
        assert len(self.states) == len(self.maps) # otherwise we should do self._new_states()
        assert len(self.predicates) == self._n_predicates # otherwise we should do self._new_predicates()
        print(f'_new_separator: pos={sorted(pos)}, neg={sorted(neg)}, sharp={sorted(sharp)}')
        if len(neg) == 0:
            return TrueExpr
        if len(pos) == 0:
            return FalseExpr
        for i in sorted(neg):
            print(f'  trying maps[{i}]')
            p = self.maps[i].separate(pos, neg, sharp) # TODO neg - {i} ??, doesn't seem important, but should check that it isn't
            if p is not None:
                return self.maps[i].to_clause(p)
        return None

def cdcl_invariant(solver: Solver) -> str:
    '''this implementation of "BMC for invariants" does not use Set Cover
    and does not try to do something smart about the permutation
    symmetry betwen predicates. It tries to be close, in spirit, to
    BMC by "unroll and cdcl", without trying to localize decisions of
    conflicts to specific predicates
    '''
    prog = syntax.the_program
    global cache_path
    cache_path = Path(utils.args.filename).with_suffix('.cache')
    load_caches()

    safety = tuple(inv.expr for inv in prog.invs() if inv.is_safety)
    def safe(s: State) -> bool:
        return all(eval_in_state(solver, s, p) for p in safety)

    states : List[State] = []
    reachable: List[int] = []
    backward_reachable: List[int] = []
    transitions: List[Tuple[int, int]] = []
    predicates: List[Predicate] = []
    sharp_predicates: FrozenSet[int] = frozenset()
    invariant: FrozenSet[int] = frozenset()

    def alpha_sharp(states: Collection[State]) -> Sequence[Expr]:
        return sorted(
            alpha_from_predicates(
                solver,
                states,
                [predicates[i] for i in sharp_predicates],
                #list(chain(safety, (predicates[i] for i in sharp_predicates))), # TODO: safety shoudn't be special
                ),
            key=lambda x: (len(str(x)),str(x))
        )

    k = 0
    K = 0
    xs: List[List[z3.ExprRef]] = [] # xs[i][j] - state i satisfied by predicate j
    cs: List[List[z3.ExprRef]] = [] # cs[i][j] - state i satisfied by predicates j, j+1, ..., so cs[i][0] means state i is satisfied by the inductive invariant
    rs: List[z3.ExprRef] = [] # rs[i] means predicate i is sharp

    sm = SeparabilityMap(states, predicates)
    z3s = z3.Solver()

    def add_inseparability(j: int, pos: FrozenSet[int], neg: FrozenSet[int], sharp: FrozenSet[int]) -> None:
        assert len(pos) > 0 and len(neg) > 0
        z3s.add(z3.Or(*chain(
            (z3.Not(xs[i][j]) for i in sorted(pos)),
            (xs[i][j] for i in sorted(neg)),
            (z3.Not(rs[i]) for i in sorted(sharp)),
        )))
    def add_state(s: State) -> int:
        i = len(states)
        states.append(s)
        xs.append([z3.Bool(f'x_{i}_{j}') for j in range(K)])
        cs.append([z3.Bool(f'c_{i}_{j}') for j in range(K + 1)])
        for j in range(K):
            z3s.add(cs[i][j] == z3.And(xs[i][j], cs[i][j + 1]))
        if not safe(s):
            backward_reachable.append(i)
            z3s.add(z3.Not(cs[i][0]))
        return i
    def houdini(a: Sequence[Predicate]) -> Sequence[Predicate]:
        _states: List[State] = [states[i] for i in reachable]
        assert (_states, a, [], []) == forward_explore(solver, alpha_sharp, _states)
        # assert set(safety) <= set(a) # TODO: I'm not sure about the handling of the safety property in forward_explore below
        while True:
            for p in a:
                res = check_two_state_implication(solver, a, p, 'CTI')
                if res is not None:
                    prestate, poststate = res
                    i_pre = add_state(prestate)
                    _states.append(prestate)
                    i_post = add_state(poststate)
                    _states.append(poststate)
                    transitions.append((i_pre, i_post))
                    z3s.add(z3.Implies(cs[i_pre][0], cs[i_post][0]))
                    _states, a, _initials, _transitions = forward_explore(
                        # TODO: this does not resue existing states in states, and adds duplicates
                        solver,
                        alpha_sharp,
                        _states,
                    )
                    index_map: Dict[int, int] = dict()
                    for i in range(len(_states)):
                        try:
                            index_map[i] = states.index(_states[i])
                        except ValueError:
                            index_map[i] = add_state(_states[i])
                    for i in _initials:
                        ii = index_map[i]
                        reachable.append(ii)
                        z3s.add(cs[ii][0])
                    for i, j in _transitions:
                        i_pre = index_map[i]
                        i_post = index_map[j]
                        transitions.append((i_pre, i_post))
                        z3s.add(z3.Implies(cs[i_pre][0], cs[i_post][0]))
                    break
            else:
                break
        return a

    while True:
        print(f'Current states ({len(states)} total, {len(reachable)} reachable, {len(backward_reachable)} backward reachable):')
        for i in range(len(states)):
            note = (' (reachable)' if i in reachable else
                    ' (backward reachable)' if i in backward_reachable else
                    '')
            print(f'states[{i}]{note}:\n{states[i]}\n' + '-' * 80)
        for i in reachable:
            if check_implication(solver, [states[i].as_onestate_formula(0)], safety) is not None:
                print(f'Found safety violation by reachable state (states[{i}]).')
                dump_caches()
                return 'UNSAFE'
        print(f'Current sharp predicates ({len(sharp_predicates)}):')
        for i in sorted(sharp_predicates):
            print(f'  predicates[{i:3}]: {predicates[i]}')


        # find an invariant that meets the currently known states,
        # learning new inseparability constraints, and possibly
        # increasing k and adding new sharp predicates
        while True:
            print(f'Finding new consistent invariant with {k} predicates', end='... ')
            z3res = z3s.check(
                *(cs[i][k] for i in range(len(states))),
                *(rs[i] for i in sharp_predicates),
            )
            assert z3res in (z3.unsat, z3.sat)
            print(z3res)
            if z3res == z3.unsat:
                print(f'No inductive invariant with {k} predicates, increasing bound')
                print('-' * 80 + f'\n{z3s}\n' + '-' * 80)
                k += 1
                assert k < 20
                if k > K:
                    for i, _ in enumerate(states):
                        xs[i].append(z3.Bool(f'x_{i}_{k - 1}'))
                        cs[i].append(z3.Bool(f'c_{i}_{k}'))
                        z3s.add(cs[i][k - 1] == z3.And(xs[i][k - 1], cs[i][k]))
                    for pos, neg, sharp in sm.inseparable:
                        add_inseparability(k - 1, pos, neg, sharp)
                    K += 1
                    assert K == k
            else:
                z3m = z3s.model()
                ps: List[Predicate] = []
                for j in range(k):
                    pos = frozenset(i for i in range(len(states)) if z3.is_true(z3m[xs[i][j]]))
                    neg = frozenset(i for i in range(len(states)) if z3.is_false(z3m[xs[i][j]]))
                    print(f'Trying to separate: pos={sorted(pos)}, neg={sorted(neg)}, sharp={sorted(sharp_predicates)}')
                    p = sm.separate(pos, neg, sharp_predicates)
                    if isinstance(p, Predicate):
                        print(f'Found separator: {p}')
                        # check if p is sharp or not
                        sharp_p = minimize_clause(p, [states[i] for i in reachable])
                        if sharp_p not in predicates:
                            print(f'Found new sharp predicate: {sharp_p}')
                            i = len(predicates)
                            predicates.append(sharp_p)
                            sharp_predicates |= {i}
                            rs.append(z3.Bool(f'r_{i}'))
                            # try to grow reachable states based on new sharp predicate
                            reachable_states, a, _, _ = forward_explore( # ignoring initial and transitions, ass all these state are simply reachable
                                solver,
                                alpha_sharp,
                                [states[i] for i in reachable],
                            )
                            if len(reachable_states) > len(reachable):
                                # we eliminated a predicate with a reachable state
                                assert len(a) < len(sharp_predicates)
                                for s in reachable_states[len(reachable):]:
                                    print(f'Found new reachable state:\n{s}\n' + '-' * 80)
                                    i = add_state(s)
                                    reachable.append(i)
                                    z3s.add(cs[i][0])
                                sharp_predicates = frozenset(i for i, p in enumerate(predicates) if p in a)
                                print(f'Found new reachable states, resetting k to 0')
                                k = 0
                                break
                            # TODO: maybe we should do Houdini here. This would be eager on the Houdini process
                            a = houdini(a)
                        if sharp_p != p:
                            break  # TODO: should we continue rather than break ?
                        else:
                            ps.append(p)
                    else:
                        pos, neg, sharp = p
                        print(f'Learned new inseparability: pos={sorted(pos)}, neg={sorted(neg)}, sharp={sorted(sharp)}')
                        for jj in range(K):
                            add_inseparability(jj, pos, neg, sharp)
                        break  # TODO: should we continue rather than break ?
                else:
                    assert len(ps) == k
                    inv = ps
                    break

        # now inv is a list of predicates whos conjunction does not have a CTI in states
        print(f'Candidate inductive invariant ({len(inv)} predicates) is:' if len(inv) > 0 else 'Candidate inductive invariant is true')
        for p in sorted(inv, key=lambda x: len(str(x))):
            print(f'  {p}')

        reachable_states, a,_ ,_ = forward_explore(
            solver,
            alpha_sharp,
            [states[i] for i in reachable],
        )
        assert len(reachable_states) == len(reachable)
        assert len(a) == len(sharp_predicates)


        # # we need to check for CTIs
        # # TODO: actually do Houdini and not just one CTI, maybe learn somethings to be inductive
        # for i, p in enumerate(inv):
        #     res = check_two_state_implication(solver, inv, p, 'CTI')
        #     if res is not None:
        #         prestate, poststate = res
        #         i_pre = add_state(prestate)
        #         if i < len(safety):
        #             assert p == safety[i]
        #             backward_reachable.append(i_pre)
        #             z3s.add(z3.Not(cs[i_pre][0]))
        #         else:
        #             i_post = add_state(poststate)
        #             transitions.append((i_pre, i_post))
        #             z3s.add(z3.Implies(cs[i_pre][0], cs[i_post][0]))
        #         break
        # else:
        #     print(f'Inductive invariant with {len(inv)} predicates found:')
        #     for p in sorted(inv, key=lambda x: (len(str(x)),str(x))):
        #         print(f'  {p}')
        #     dump_caches()
        #     return 'SAFE'

        # first check if inv |= wp(safety)
        for p in safety:
            res = check_two_state_implication(solver, inv, p, 'safety CTI')
            if res is not None:
                prestate, poststate = res
                i_pre = add_state(prestate)
                i_post = add_state(poststate)
                transitions.append((i_pre, i_post))
                z3s.add(z3.Implies(cs[i_pre][0], cs[i_post][0]))
                break
        else:
            print('Invariant implies wp(safety)')


        # run Houdini over the sharp predicates
        # TODO: do it in a more stratified manner to collect frames
        # TODO: learn transitions directly from forward_explore
        a = houdini(a)
        print(f'Current inductive invariant ({len(a)} predicates) is:' if len(a) > 0 else 'Current inductive invariant is true')
        for p in sorted(a, key=lambda x: len(str(x))):
            print(p)
        if len(a) > 0 and check_implication(solver, a, safety) is None:
            print('Implies safety!')
            dump_caches()
            return 'SAFE'
        #inductive = frozenset(i for i, p in enumerate(predicates) if p in a)



def enumerate_reachable_states(s: Solver) -> None:
    # TODO: this function is hacky for paxos, clean up
    # TODO: this does not use caches at all
    prog = syntax.the_program
    states: List[Model] = []
    with s:
        for sort in prog.sorts():
            b = 2
            # an old hack for paxos that is commented out below
            # if sort.name == 'round':
            #     b = 3
            # else:
            #     b = 2
            print(f'bounding {sort} to candinality {b}')
            s.add(s._sort_cardinality_constraint(sort.to_z3(), b))

        unknown = False

        def block_state(t: Z3Translator, m: Model) -> None:
            # TODO: with the diagram, smaller states block larger
            # ones, but with onestate it's slower (paxos can't get
            # beyond initial states with 2 of everything). we should
            # collect states by the sizes of their universe

            # s.add(z3.Not(t.translate_expr(m.as_diagram(0).to_ast(), old=False)))
            s.add(z3.Not(t.translate_expr(m.as_onestate_formula(0), old=False)))

        print('looking for initial states')
        with s:
            t = s.get_translator(KEY_ONE)
            for init in prog.inits():
                s.add(t.translate_expr(init.expr))
            while True:
                print(f'{len(states)} total states so far')
                res = s.check()
                if res == z3.unsat:
                    break
                elif res == z3.unknown:
                    unknown = True
                    break
                else:
                    m = Model.from_z3([KEY_ONE], s.model(minimize=False))
                    states.append(m)
                    block_state(t, m)
        print(f'done finding initial states! found {len(states)} states')

        print('looking for transitions to new states')
        with s:
            t = s.get_translator(KEY_NEW, KEY_OLD)
            for state in states:
                block_state(t, m)

            worklist = list(product(states, prog.transitions()))
            while len(worklist) > 0:
                print(f'worklist has length {len(worklist)}')
                state, ition = worklist.pop()
                new_states = []
                with s:
                    s.add(t.translate_expr(state.as_onestate_formula(0), old=True))
                    s.add(t.translate_transition(ition))

                    while True:
                        res = s.check()
                        if res == z3.unsat:
                            break
                        elif res == z3.unknown:
                            unknown = True
                            break

                        m = Model.from_z3([KEY_NEW, KEY_OLD], s.model(minimize=False))
                        new_states.append(m)
                        block_state(t, m)
                for state in new_states:
                    worklist.extend([(state, x) for x in prog.transitions()])
                    block_state(t, m)
                states.extend(new_states)
                if len(new_states) > 0:
                    print(f'found {len(new_states)} new states via transition {ition.name}')
                    print(f'{len(states)} total states so far')
                    # TODO: get this file from command line or somewhere that's at least per example
                    # with open('reachable-states.cache', 'wb') as cache_file:
                    #     pickle.dump(states, cache_file)

        print(f'exhausted all transitions from known states! found {len(states)} states')
        for state in states:
            print('-' * 80 + '\n' + str(state))

        if unknown:
            print('encountered unknown! all bets are off.')


def add_argparsers(subparsers: argparse._SubParsersAction) -> Iterable[argparse.ArgumentParser]:
    result : List[argparse.ArgumentParser] = []

    # forward_explore_inv
    s = subparsers.add_parser('pd-forward-explore-inv', help='Forward explore program w.r.t. its invariant')
    s.set_defaults(main=forward_explore_inv)
    result.append(s)

    # enumerate_reachable_states
    s = subparsers.add_parser('enumerate-reachable-states')
    s.set_defaults(main=enumerate_reachable_states)
    result.append(s)

    # repeated_houdini
    s = subparsers.add_parser('pd-repeated-houdini', help='Run the repeated Houdini algorith in the proof space')
    s.set_defaults(main=repeated_houdini)
    s.add_argument('--sharp', action=utils.YesNoAction, default=True,
                   help='search for sharp invariants')
    result.append(s)

    # cdcl_invariant
    s = subparsers.add_parser('pd-cdcl-invariant', help='Run the "CDCL over invariants" algorithm')
    s.set_defaults(main=cdcl_invariant)
    result.append(s)

    for s in result:
        s.add_argument('--unroll-to-depth', type=int, help='Unroll transitions to given depth during exploration')

    return result
