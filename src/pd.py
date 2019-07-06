'''
This file contains code for the Primal Dual research project
'''

from __future__ import annotations

import argparse
import itertools
from itertools import product, chain, combinations, repeat
from functools import reduce
from collections import defaultdict
from pathlib import Path
import pickle
import sys
import os
import math
import multiprocessing

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
            '_cache_map_clause_state_interaction',
            '_cache_dual_edge',
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
        if False: # check _cache_eval_in_state against current implementation
            for k, v in _cache_eval_in_state.items():
                if type(k) is not tuple:
                    continue
                m, p = k
                assert v == all(eval_clause_in_state(clause, m) for clause in as_clauses(p)), f'{p}\n=========\n{m}'
                # assert v == cheap_check_implication([m.as_onestate_formula(0)], [p]), f'{p}\n=========\n{m}'
            sys.exit(0)

# signal handler to dump caches
import signal
def handler(signum: Any, frame: Any) -> None:
    print(f'\n\nSignal handler called with signal {signum}')
    dump_caches()
    print('Moving on...\n\n')
    sys.stdout.flush()
    return
# Set the signal handler and a 5-second alarm
signal.signal(signal.SIGALRM, handler)


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

def eval_clause_in_state(
        clause: Expr,
        state: State,
) -> bool:
    variables, literals = destruct_clause(clause)
    def ev(values: Sequence[str], lit: Expr) -> bool:
        # TODO: rewrite this with James, this is a hacky partial implementation of first-order logic semantics for class Model (written on a plane from Phoenix to SF)
        assert len(variables) == len(values)
        consts_and_vars: Dict[str, str] = dict(chain(
            ((var.name, val) for var, val in zip(variables, values)),
            ((d.name, val) for d, val in state.immut_const_interps.items()),
            ((d.name, val) for d, val in state.const_interps[0].items()),
        ))
        functions: Dict[str, Dict[Tuple[str,...], str]] = dict(
            (d.name, dict((tuple(args), val) for args, val in func))
            for d, func in chain(state.immut_func_interps.items(), state.func_interps[0].items())
        )
        relations: Dict[str, Dict[Tuple[str,...], bool]] = dict(
            (d.name, dict((tuple(args), val) for args, val in func))
            for d, func in chain(state.immut_rel_interps.items(), state.rel_interps[0].items())
        )
        def get_term(t: Expr) -> str:
            if isinstance(t, Id):
                assert t.name in consts_and_vars, f'{t.name}\n' + '='*80 + f'\n{state}\n'
                return consts_and_vars[t.name]
            elif isinstance(t, AppExpr):
                assert t.callee in functions, f'{t.callee}\n' + '='*80 + f'\n{state}\n'
                return functions[t.callee][tuple(get_term(a) for a in t.args)]
            else:
                assert False, t
        if isinstance(lit, Bool):
            return lit.val
        elif isinstance(lit, UnaryExpr):
            assert lit.op == 'NOT', lit
            return not ev(values, lit.arg)
        elif isinstance(lit, BinaryExpr):
            assert lit.op in ('EQUAL', 'NOTEQ'), lit
            eq = get_term(lit.arg1) == get_term(lit.arg2)
            return eq if lit.op == 'EQUAL' else not eq
        elif isinstance(lit, AppExpr):
            return relations[lit.callee][tuple(get_term(a) for a in lit.args)]
        elif isinstance(lit, Id):
            # nullary relation
            assert lit.name in relations, f'{lit.name}\n' + '='*80 + f'\n{state}\n'
            return relations[lit.name][()]
        else:
            assert False, lit
    universes = []
    for v in variables:
        assert isinstance(v.sort, UninterpretedSort), v
        if v.sort.decl is not None and v.sort.decl in state.univs:
            assert v.sort.name == v.sort.decl.name, v
            universes.append(state.univs[v.sort.decl])
        else:
            # assert False, v # TODO: ask James why does this happen
            ds = [d for d in state.univs if d.name == v.sort.name]
            assert len(ds) == 1, v
            universes.append(state.univs[ds[0]])
    n = reduce(lambda x, y: x * y, [len(u) for u in universes], 1)
    # print(f'eval_clause_in_state: iterating over {n} instantiations... ', end='')
    result = all(any(ev(tup,lit) for lit in literals) for tup in product(*universes))
    # print(f'done.')
    return result

_solver: Optional[Solver] = None
def get_solver() -> Solver:
    global _solver
    if _solver is None:
        _solver = Solver()
    return _solver


def cheap_check_implication(
        hyps: Iterable[Expr],
        concs: Iterable[Expr],
) -> bool:
    s = get_solver()
    t = s.get_translator(KEY_ONE)
    with s:
        for e in hyps:
            s.add(t.translate_expr(e))
        for e in concs:
            with s:
                s.add(z3.Not(t.translate_expr(e)))
                if s.check() != z3.unsat:
                    return False
    return True


_cache_eval_in_state : Dict[Any,Any] = dict(h=0,m=0)
def eval_in_state(s: Optional[Solver], m: State, p: Expr) -> bool:
    if s is None:
        s = get_solver()
    cache = _cache_eval_in_state
    k = (m, p)
    if k not in cache:
        cache[k] = eval_clause_in_state(p, m)
        # if m.z3model is not None:
        #     try:
        #         cache[k] = eval_quant(m.z3model, s.get_translator(m.keys[0]).translate_expr(p))
        #     except:
        #         print(m)
        #         raise
        # else:
        #     cache[k] = cheap_check_implication([m.as_onestate_formula(0)], [p])

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
    # inits = tuple(init.expr for init in prog.inits())
    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # must be in CNF for use in eval_in_state
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


def is_substructure(s: State, t: State) -> bool:
    '''Returns true if s is a sub structure of t'''
    sorts_s = sorted(s.univs.keys(), key=str)
    sorts_t = sorted(t.univs.keys(), key=str)
    cheap_check = [str(x) for x in sorts_s] == [str(x) for x in sorts_t] and all(
        len(s.univs[k1]) <= len(t.univs[k2])
        for k1, k2 in zip(sorts_s, sorts_t)
    )
    if not cheap_check:
        return False
    diag_s = s.as_diagram(0).to_ast()
    diag_t = t.as_diagram(0).to_ast()
    if diag_s == diag_t:
        return True
    return cheap_check_implication([diag_t], [diag_s])


_cache_two_state_implication : Dict[Any,Any] = dict(h=0,r=0)
_cache_transitions: List[Tuple[State,State]] = []
def isomorphic_states(solver: Solver, s: State, t: State) -> bool:
    x = s.as_onestate_formula(0)
    y = t.as_onestate_formula(0)
    return x == y # or cheap_check_implication([], [Iff(x, y)])
    # TODO: we need to figure this out. are two isomorphic structures the same state or no? this showed up in:
    # time ./src/mypyvy.py pd-repeated-houdini --no-sharp --clear-cache examples/lockserv.pyv > 1
    # time ./src/mypyvy.py pd-repeated-houdini --no-sharp --clear-cache-memo --cache-only-discovered examples/lockserv.pyv > 2
    # this can be fixed by checking equivalence between onestate formulas, but this is very slow
def check_two_state_implication_multiprocessing_helper(
        seed: Optional[int],
        s: Optional[Solver],
        old_hyps: Iterable[Expr],
        new_conc: Expr,
        minimize: Optional[bool] = None,
) -> Optional[Tuple[Model, Model]]:
    if s is None:
        s = Solver()
    if seed is not None:
        print(f'PID={os.getpid()} setting z3 seed to {seed}')
        # z3.set_param('smt.random_seed', seed) -- this probably needs to be called before creating the solver
        # TODO: figure out if this is a good way to set the seed
        s.z3solver.set(seed=seed)  # type: ignore  # TODO: fix typing

    res = check_two_state_implication_all_transitions(s, old_hyps, new_conc, minimize)
    if seed is not None:
        print(f'PID={os.getpid()} z3 returned {"unsat" if res is None else "sat"}')
    if res is None:
        return None
    else:
        z3m, _ = res
        prestate = Model.from_z3([KEY_OLD], z3m)
        poststate = Model.from_z3([KEY_NEW, KEY_OLD], z3m)
        return (prestate, poststate)
def check_two_state_implication_multiprocessing(
        s: Solver,
        old_hyps: Iterable[Expr],
        new_conc: Expr,
        minimize: Optional[bool] = None,
) -> Optional[Tuple[Model, Model]]:
    # this function uses multiprocessing to start multiple solvers
    # with different random seeds and return the first result obtained
    if utils.args.cpus is None or utils.args.cpus == 1:
        return check_two_state_implication_multiprocessing_helper(None, s, old_hyps, new_conc, minimize)
    with multiprocessing.Pool(utils.args.cpus) as pool:
        results = []
        for i in itertools.count():
            if i < utils.args.cpus:
                results.append(pool.apply_async(
                    check_two_state_implication_multiprocessing_helper,
                    (i, None, list(old_hyps), new_conc, minimize)
                ))
            results[0].wait(1)
            ready = [r for r in results if r.ready()]
            if len(ready) > 0:
                return ready[0].get(1)  # the context manager of pool will terminate the processes
    assert False
def check_two_state_implication(
        s: Solver,
        precondition: Union[Iterable[Expr], State],
        p: Expr,
        msg: str = 'transition',
        minimize: Optional[bool] = None,
) -> Optional[Tuple[State,State]]:
    prog = syntax.the_program
    # inits = tuple(init.expr for init in prog.inits())
    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # must be in CNF for use in eval_in_state

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
            res = check_two_state_implication_multiprocessing(
                s,
                [precondition.as_onestate_formula(0)] if isinstance(precondition, State) else precondition,
                p,
                minimize
            )
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
                prestate, poststate = res
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


_cache_dual_edge: Dict[Any,Any] = dict(h=0,r=0)
# TODO: cache valid dual edges like we cache transitions
def check_dual_edge(
        s: Solver,
        ps: Tuple[Expr,...],
        qs: Tuple[Expr,...],
        msg: str = 'cti',
) -> Tuple[Optional[Tuple[State, State]], Optional[Tuple[Expr,...]]]:
    '''
    this checks if ps /\ qs |= wp(ps -> qs)
    note it does not check if init |= qs, but for now we assert it
    '''
    prog = syntax.the_program
    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # must be in CNF for use in eval_in_state
    k = (ps, qs)
    cache = _cache_dual_edge
    print(f'check_dual_edge: starting to check the following edge:')
    for p in ps:
        print(f'  {p}')
    print('  -->')
    for q in qs:
        print(f'  {q}')
    assert cheap_check_implication(inits, ps)
    assert cheap_check_implication(inits, qs)
    def check(ps_i: FrozenSet[int], minimize: bool) -> Optional[Tuple[z3.ModelRef, DefinitionDecl]]:
        _ps = [ps[i] for i in sorted(ps_i)]
        print(f'check_dual_edge: calling z3... ', end='')
        res =  check_two_state_implication_all_transitions(
            s,
            chain(_ps, qs),
            Implies(And(*_ps), And(*qs)),
            minimize=minimize,
        )
        print(f'done')
        return res
    if k not in cache:
        if utils.args.cache_only:
            assert False
        for prestate, poststate in _cache_transitions:
            if (    all(eval_in_state(s, prestate,  p) for p in ps) and
                    all(eval_in_state(s, prestate,  q) for q in qs) and
                    all(eval_in_state(s, poststate, p) for p in ps) and
                not all(eval_in_state(s, poststate, q) for q in qs)):
                # TODO: we're not really minimizing the cti here... probably fine
                cache[k] = ((prestate, poststate), None)
                cache['r'] += 1
                print(f'check_dual_edge: found previous {msg} violating dual edge')
                # print('-'*80 + '\n' + str(poststate) + '\n' + '-'*80)
                break
        else:
            ps_i = frozenset(range(len(ps)))
            res = check(ps_i, True)
            if res is not None:
                if utils.args.cache_only_discovered:
                    assert False
                z3m, _ = res
                prestate = Model.from_z3([KEY_OLD], z3m)
                # poststate = Model.from_z3([KEY_NEW, KEY_OLD], z3m)
                poststate = Model.from_z3([KEY_NEW], z3m) # TODO: can we do this? this seems better than dragging the prestate along
                print(f'check_dual_edge: found new {msg} violating dual edge')
                _cache_transitions.append((prestate, poststate))
                for state in (prestate, poststate):
                    if all(eval_in_state(s, state, p) for p in inits):
                        _cache_initial.append(state)
                    # TODO: actually, we should first try to get (from Z3) a transition where the prestate is initial
                cache[k] = ((prestate, poststate), None)
            else:
                # minimize ps_i
                # TODO: use unsat cores?
                for i in sorted(ps_i, reverse=True): # TODO: reverse or not?
                    if i in ps_i and check(ps_i - {i}, False) is None:
                        ps_i -= {i}
                ps = tuple(ps[i] for i in ps_i)
                print(f'check_dual_edge: found new valid dual edge:')
                for p in ps:
                    print(f'  {p}')
                print('  -->')
                for q in qs:
                    print(f'  {q}')
                cache[k] = (None, ps)

        if len(cache) % 100 == 1:
            # dump_caches()
            print(f'_cache_dual_edge length is {len(cache)}, h/r is {cache["h"]}/{cache["r"]}')

    else:
        cti, ps = cache[k]
        if cti is not None:
            print(f'check_dual_edge: found cached {msg} violating dual edge')
        else:
            print(f'check_dual_edge: found cached valid dual edge:')
            for p in ps:
                print(f'  {p}')
            print('  -->')
            for q in qs:
                print(f'  {q}')
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


# cache and helpers for multiprocessing for map_clause_state_interaction
_cache_map_clause_state_interaction: Dict[Tuple[Tuple[SortedVar,...], Tuple[Expr,...], Union[State, Expr]] ,Tuple[List[FrozenSet[int]], List[FrozenSet[int]]]] = dict()
# TODO: --cache-only checks for this cache (nothign right now)
def _map_clause_state_interaction_helper(vls: Tuple[Tuple[SortedVar,...], Tuple[Expr,...], Union[State, Expr]]) -> Tuple[List[FrozenSet[int]], List[FrozenSet[int]]]:
    if isinstance(vls[2], State):
        all_mss = map_clause_state_interaction_instantiate(vls[0], vls[1], vls[2])
        if False: # TODO: run at some point to verify
            _, all_mss2 = map_clause_state_interaction(*vls)
            assert len(all_mss) == len(set(all_mss))
            assert len(all_mss2) == len(set(all_mss2))
            assert set(all_mss) == set(all_mss2), (sorted(all_mss), sorted(all_mss2))
        return [], all_mss
    else:
        return map_clause_state_interaction(*vls)
def multiprocessing_map_clause_state_interaction(work: List[Tuple[
        Tuple[SortedVar,...],
        Tuple[Expr,...],
        Union[State, Expr],
]]) -> List[Tuple[List[FrozenSet[int]], List[FrozenSet[int]]]]:
    real_work = [k for k in work if k not in _cache_map_clause_state_interaction]
    if False:
        # for debugging, compare results from cache to map_clause_state_interaction_instantiate
        for k in work:
            if k in _cache_map_clause_state_interaction and isinstance(k[2], State):
                all_mus, all_mss = _cache_map_clause_state_interaction[k]
                all_mss2 = map_clause_state_interaction_instantiate(k[0], k[1], k[2])
                assert len(all_mss) == len(set(all_mss))
                assert len(all_mss2) == len(set(all_mss2))
                assert set(all_mss) == set(all_mss2), (sorted(all_mss), sorted(all_mss2))
    if len(real_work) > 0:
        if utils.args.cpus is None:
            n = 1
        else:
            n = min(utils.args.cpus, len(real_work))
        if n > 1:
            with multiprocessing.Pool(n) as pool:
                results = pool.map_async(
                    _map_clause_state_interaction_helper,
                    real_work,
                ).get(9999999) # see: https://stackoverflow.com/a/1408476
        else:
            results = list(map(_map_clause_state_interaction_helper, real_work))
        for k, v in zip(real_work, results):
            _cache_map_clause_state_interaction[k] = v
    return [_cache_map_clause_state_interaction[k] for k in work]
def map_clause_state_interaction(variables: Tuple[SortedVar,...],
                                 literals: Tuple[Expr,...],
                                 state_or_predicate: Union[State, Expr],
) -> Tuple[List[FrozenSet[int]], List[FrozenSet[int]]]:
    print(f' (PID={os.getpid()}) ', end='')
    cache = _cache_map_clause_state_interaction
    k = (variables, literals, state_or_predicate)
    if k in cache:
        print('found in cache!')
        return cache[k]

    def to_clause(s: Iterable[int]) -> Expr:
        lits = [literals[i] for i in sorted(s)]
        free = set(chain(*(lit.free_ids() for lit in lits)))
        vs = [v for v in variables if v.name in free]
        return Forall(vs, Or(*lits)) if len(vs) > 0 else Or(*lits)

    n = len(literals)
    all_n = frozenset(range(n))
    solver = Solver()
    t = solver.get_translator(KEY_ONE)
    solver.add(t.translate_expr(
        state_or_predicate if isinstance(state_or_predicate, Expr) else
        state_or_predicate.as_onestate_formula(0)
    ))

    # there is some craziness here about mixing a mypyvy clause with z3 indicator variables
    # some of this code is taken out of syntax.Z3Translator.translate_expr
    lit_indicators = tuple(z3.Bool(f'@lit_{i}') for i in range(n))
    clause_indicator = z3.Bool('@clause')
    # TODO: why can't top clause be quantifier free? it should be possible
    top_clause = to_clause(all_n)
    assert isinstance(top_clause, QuantifierExpr)
    assert isinstance(top_clause.body, NaryExpr)
    assert top_clause.body.op == 'OR'
    assert tuple(literals) == tuple(top_clause.body.args)
    bs = t.bind(top_clause.binder)
    with t.scope.in_scope(top_clause.binder, bs):
        body = z3.Or(*(
            z3.And(lit_indicators[i], t.translate_expr(lit))
            for i, lit in enumerate(literals)
        ))
    solver.add(clause_indicator == z3.ForAll(bs, body))

    # find all mss - maximal subclauses not satisfied by the state / implied by predicate
    all_mss: List[FrozenSet[int]] = []
    while True:
        indicators = [z3.Not(clause_indicator)]
        res = solver.check(indicators)
        assert res in (z3.unsat, z3.sat)
        if res == z3.unsat:
            break
        z3m = solver.model(indicators, minimize=False)
        assert z3.is_false(z3m[clause_indicator])
        # grow the set of indicator variables set to true
        forced_to_true = set(
            i for i, v in enumerate(lit_indicators)
            if not z3.is_false(z3m[v])
        )
        assert solver.check(indicators + [lit_indicators[j] for j in sorted(forced_to_true)]) == z3.sat
        for i in range(n):
            if i not in forced_to_true:
                res = solver.check(indicators + [lit_indicators[j] for j in sorted(forced_to_true | {i})])
                assert res in (z3.unsat, z3.sat)
                if res == z3.sat:
                    forced_to_true.add(i)
        assert solver.check(indicators + [lit_indicators[j] for j in sorted(forced_to_true)]) == z3.sat
        mss = frozenset(forced_to_true)
        print(f'mss({len(mss)}) ', end='')
        # print(f'mss({to_clause(mss)}) ')
        all_mss.append(mss)
        # block down
        solver.add(z3.Or(*(lit_indicators[i] for i in sorted(all_n - mss))))
    print(f'total mss: {len(all_mss)}')
    assert len(all_mss) > 0 or state_or_predicate == FalseExpr

    # find all mus - minimal subclauses satisfied by the state (cannot do this for predicate like this)
    all_mus: List[FrozenSet[int]] = []
    if isinstance(state_or_predicate, State) and False:  # not really needed if we have all the mss, TODO: should examine why so many mus and not so many mss, could be a bug
        while True:
            indicators = [clause_indicator]
            res = solver.check(indicators)
            assert res in (z3.unsat, z3.sat)
            if res == z3.unsat:
                break
            z3m = solver.model(indicators, minimize=False)
            assert z3.is_true(z3m[clause_indicator])
            # grow the set of indicator variables set to false
            forced_to_false = set(
                i for i, v in enumerate(lit_indicators)
                if not z3.is_true(z3m[v])
            )
            assert solver.check(indicators + [z3.Not(lit_indicators[j]) for j in sorted(forced_to_false)]) == z3.sat
            for i in range(n):
                if i not in forced_to_false:
                    res = solver.check(indicators + [z3.Not(lit_indicators[j]) for j in sorted(forced_to_false | {i})])
                    assert res in (z3.unsat, z3.sat)
                    if res == z3.sat:
                        forced_to_false.add(i)
            assert solver.check(indicators + [z3.Not(lit_indicators[j]) for j in sorted(forced_to_false)]) == z3.sat
            mus = frozenset(all_n - forced_to_false)
            # print(f'mus({len(mus)}) ', end='')
            print(f'mus({to_clause(mus)}) ')
            all_mus.append(mus)
            # block up
            solver.add(z3.Or(*(z3.Not(lit_indicators[i]) for i in sorted(mus))))
        print(f'total mus: {len(all_mus)}')

    cache[k] = (all_mus, all_mss)
    return cache[k]

def map_clause_state_interaction_instantiate(
        variables: Tuple[SortedVar,...],
        literals: Tuple[Expr,...],
        state: State,
) -> List[FrozenSet[int]]:
    '''Return a list of maximal subclauses of the given clause (indices to
    literals) that are violated by the given state (equivalent to
    all_mss computed by map_clause_state_interaction), using explicit
    iteration over all quantifier instantiations.
    '''
    def ev(values: Sequence[str], lit: Expr) -> bool:
        # TODO: rewrite this with James, this is a hacky partial implementation of first-order logic semantics for class Model (written on a plane from Phoenix to SF)
        assert len(variables) == len(values)
        consts_and_vars: Dict[str, str] = dict(chain(
            ((var.name, val) for var, val in zip(variables, values)),
            ((d.name, val) for d, val in state.immut_const_interps.items()),
            ((d.name, val) for d, val in state.const_interps[0].items()),
        ))
        functions: Dict[str, Dict[Tuple[str,...], str]] = dict(
            (d.name, dict((tuple(args), val) for args, val in func))
            for d, func in chain(state.immut_func_interps.items(), state.func_interps[0].items())
        )
        relations: Dict[str, Dict[Tuple[str,...], bool]] = dict(
            (d.name, dict((tuple(args), val) for args, val in func))
            for d, func in chain(state.immut_rel_interps.items(), state.rel_interps[0].items())
        )
        def get_term(t: Expr) -> str:
            if isinstance(t, Id):
                return consts_and_vars[t.name]
            elif isinstance(t, AppExpr):
                return functions[t.callee][tuple(get_term(a) for a in t.args)]
            else:
                assert False, t
        if isinstance(lit, Bool):
            return lit.val
        elif isinstance(lit, UnaryExpr):
            assert lit.op == 'NOT', lit
            return not ev(values, lit.arg)
        elif isinstance(lit, BinaryExpr):
            assert lit.op in ('EQUAL', 'NOTEQ'), lit
            eq = get_term(lit.arg1) == get_term(lit.arg2)
            return eq if lit.op == 'EQUAL' else not eq
        elif isinstance(lit, AppExpr):
            return relations[lit.callee][tuple(get_term(a) for a in lit.args)]
        elif isinstance(lit, Id):
            # nullary relation
            return relations[lit.name][()]
        else:
            assert False, lit
    result: List[FrozenSet[int]] = []
    universes = []
    for v in variables:
        assert isinstance(v.sort, UninterpretedSort), v
        if v.sort.decl is not None and v.sort.decl in state.univs:
            assert v.sort.name == v.sort.decl.name, v
            universes.append(state.univs[v.sort.decl])
        else:
            # assert False, v # TODO: ask James why does this happen
            ds = [d for d in state.univs if d.name == v.sort.name]
            assert len(ds) == 1, v
            universes.append(state.univs[ds[0]])
    n = reduce(lambda x, y: x * y, [len(u) for u in universes], 1)
    print(f'map_clause_state_interaction_instantiate: PID={os.getpid()}, iterating over {n} instantiations... ')
    for tup in product(*universes):
        mss = frozenset(
            i
            for i, lit in enumerate(literals)
            if not ev(tup, lit)
        )
        if not any(mss <= other for other in result):
            result = [
                other for other in result if not other <= mss
            ] + [mss]
    print(f'map_clause_state_interaction_instantiate: PID={os.getpid()}, iterated over {n} instantiations, found {len(result)} MSSs')
    return result



class SubclausesMapTurbo(object):
    '''
    Class used to store a map of subclauses of a certain clause, and
    obtain subclauses that are positive and negative on some given
    states.
    '''
    def __init__(self,
                 top_clause: Expr,
                 states: List[State],  # assumed to only grow
                 predicates: List[Expr],  # assumed to only grow
                 optimize: bool = False,
    ):
        '''
        states is assumed to be a list that is increasing but never modified
        '''
        self.states = states
        self.predicates = predicates
        self.variables, self.literals = destruct_clause(top_clause)
        self.n = len(self.literals)
        self.all_n = set(range(self.n))  # used in complement fairly frequently
        self.optimize = optimize
        self.solver = z3.Optimize() if optimize else z3.Solver()  # type: ignore # TODO - fix typing
        self.lit_vs = [z3.Bool(f'lit_{i}') for i in range(self.n)]
        self.state_vs: List[z3.ExprRef] = []
        self.predicate_vs: List[z3.ExprRef] = []
        # self._new_states()
        # self._new_predicates()

    def _new_states(self) -> None:
        new = range(len(self.state_vs), len(self.states))
        if len(new) == 0:
            return
        self.state_vs.extend(z3.Bool(f's_{i}') for i in new)
        print(f'Mapping out subclauses-state interaction with {len(new)} new states for {self.to_clause(self.all_n)}')
        total_mus = 0
        total_mss = 0
        results = multiprocessing_map_clause_state_interaction([
            (self.variables, self.literals, self.states[i])
            for i in new
        ])
        for i in new:
            # print(f'Mapping out subclauses-state interaction with states[{i}]... ', end='')
            # all_mus, all_mss = map_clause_state_interaction(self.variables, self.literals, self.states[i])
            all_mus, all_mss = results.pop(0)
            if len(all_mus) > 0:
                # use both all_mus and all_mss
                for v in all_mus:
                    self.solver.add(z3.Or(self.state_vs[i], *(
                        z3.Not(self.lit_vs[j]) for j in sorted(v)
                    )))
                for v in all_mss:
                    self.solver.add(z3.Or(z3.Not(self.state_vs[i]), *(
                        self.lit_vs[j] for j in sorted(self.all_n - v)
                    )))
            else:
                # use only all_mss
                self.solver.add(self.state_vs[i] == z3.And(*(
                    z3.Or(*(
                        self.lit_vs[j] for j in sorted(self.all_n - v)
                    ))
                    for v in all_mss
                )))
            # print(f'done subclauses-state (cdnf={len(all_mus) + len(all_mss)}, mus={len(all_mus)}, mss={len(all_mss)})')
            total_mus += len(all_mus)
            total_mss += len(all_mss)
            if False: # just for development, checking against much slower implementation
                print(f'checking against old implementation... ', end='')
                _all_mus: List[FrozenSet[int]] = []
                _all_mss: List[FrozenSet[int]] = []
                def f(s: Set[int]) -> bool:
                    return eval_in_state(None, self.states[i], self.to_clause(s))
                for k, vv in marco(self.n, f):
                    if k == 'MUS':
                        _all_mus.append(frozenset(vv))
                    elif k == 'MSS':
                        _all_mss.append(frozenset(vv))
                    else:
                        assert False
                assert set(all_mus) == set(_all_mus)
                assert set(all_mss) == set(_all_mss)
                print(f'ok')
        print(f'Done subclauses-states (total_cdnf={total_mus + total_mss}, total_mus={total_mus}, total_mss={total_mss})')

    def _new_predicates(self) -> None:
        new = range(len(self.predicate_vs), len(self.predicates))
        if len(new) == 0:
            return
        self.predicate_vs.extend(z3.Bool(f'p_{i}') for i in new)
        print(f'Mapping out subclauses-predicate interaction with {len(new)} new predicates for {self.to_clause(self.all_n)}')
        total_mus = 0
        total_mss = 0
        results = multiprocessing_map_clause_state_interaction([
            (self.variables, self.literals, self.predicates[i])
            for i in new
        ])
        for i in new:
            all_mus, all_mss = results.pop(0)
            if len(all_mus) > 0:
                # use only all_mus
                for v in all_mus:
                    # print(f'  {self.predicates[i]} |= {self.to_clause(v)}')
                    self.solver.add(z3.Or(z3.Not(self.predicate_vs[i]), *(
                        z3.Not(self.lit_vs[j]) for j in sorted(v)
                    )))
            else:
                # use only all_mss
                self.solver.add(z3.Or(z3.Not(self.predicate_vs[i]), *(
                    z3.And(*(
                        z3.Not(self.lit_vs[j]) for j in sorted(self.all_n - v)
                    ))
                    for v in all_mss
                )))
            # print(f'done subclauses-predicate (cdnf={len(all_mus) + len(all_mss)}, mus={len(all_mus)}, mss={len(all_mss)})')
            total_mus += len(all_mus)
            total_mss += len(all_mss)
            if False: # just for development, checking against much slower implementation
                _all_mus: List[FrozenSet[int]] = []
                _all_mss: List[FrozenSet[int]] = []
                def f(s: Set[int]) -> bool:
                    # TODO: use unsat cores here
                    return cheap_check_implication([self.predicates[i]], [self.to_clause(s)])
                for k, vv in marco(self.n, f):
                    if k == 'MUS':
                        _all_mus.append(frozenset(vv))
                    elif k == 'MSS':
                        _all_mss.append(frozenset(vv))
                    else:
                        assert False
                assert len(all_mus) == 0 or set(all_mus) == set(_all_mus)
                assert set(all_mss) == set(_all_mss)
                print(f'ok')
        print(f'Done subclauses-predicates (total_cdnf={total_mus + total_mss}, total_mus={total_mus}, total_mss={total_mss})')

    def separate(self,
                 pos: Collection[int] = frozenset(),
                 neg: Collection[int] = frozenset(),
                 ps: Collection[int] = frozenset(),
                 soft_pos: Collection[int] = frozenset(),
                 soft_neg: Collection[int] = frozenset(),
                 soft_ps: Collection[int] = frozenset(),
    ) -> Optional[FrozenSet[int]]:
        '''
        find a subclause that is positive on pos and negative on neg. pos,neg are indices to self.states.

        TODO: to we need an unsat core in case there is no subclause?
        '''
        self._new_states()
        self._new_predicates()
        assert all(0 <= i < len(self.states) for i in chain(pos, neg, soft_pos, soft_neg))
        assert all(0 <= i < len(self.predicates) for i in chain(ps, soft_ps))
        sep = list(chain(
            (self.state_vs[i] for i in sorted(pos)),
            (z3.Not(self.state_vs[i]) for i in sorted(neg)),
            (self.predicate_vs[i] for i in sorted(ps)),
        ))
        soft = list(chain(
            (self.state_vs[i] for i in sorted(soft_pos)),
            (z3.Not(self.state_vs[i]) for i in sorted(soft_neg)),
            (self.predicate_vs[i] for i in sorted(soft_ps)),
        ))
        if len(soft) > 0:
            assert self.optimize
            self.solver.push()
            for c in soft:
                self.solver.add_soft(c)
        res = self.solver.check(*sep)
        assert res in (z3.unsat, z3.sat)
        if res == z3.unsat:
            if len(soft) > 0:
                self.solver.pop()
            return None
        # minimize for strongest possible clause
        # TODO: just use z3's Optimize instead of minimizing manually
        model = self.solver.model()
        forced_to_false = set(
            i for i, v in enumerate(self.lit_vs)
            if not z3.is_true(model[v])
        )
        for i in range(self.n):
            if i not in forced_to_false:
                res = self.solver.check(*sep, *(z3.Not(self.lit_vs[j]) for j in sorted(chain(forced_to_false, [i]))))
                assert res in (z3.unsat, z3.sat)
                if res == z3.sat:
                    forced_to_false.add(i)
        assert self.solver.check(*sep, *(z3.Not(self.lit_vs[j]) for j in sorted(forced_to_false))) == z3.sat
        result = frozenset(self.all_n - forced_to_false)
        if False:
            # just some paranoid tests
            clause = self.to_clause(result)
            assert all(eval_in_state(None, self.states[i], clause) for i in sorted(pos))
            assert all(not eval_in_state(None, self.states[i], clause) for i in sorted(neg))
            assert all(not cheap_check_implication([self.predicates[i]], [clause]) for i in sorted(ps))
        if len(soft) > 0:
            self.solver.pop()
        return result

    def to_clause(self, s: Iterable[int]) -> Expr:
        lits = [self.literals[i] for i in sorted(s)]
        free = set(chain(*(lit.free_ids() for lit in lits)))
        vs = [v for v in self.variables if v.name in free]
        return Forall(vs, Or(*lits)) if len(vs) > 0 else Or(*lits)


class MultiSubclausesMapICE(object):
    '''Class used to store a map of subclauses of several clauses, and
    obtain a conjunction of subclauses that satisfy positive,
    negative, and implication constraints on some given states.
    '''
    def __init__(self,
                 top_clauses: Sequence[Expr],
                 states: List[State],  # assumed to only grow
                 predicates: List[Expr],  # assumed to only grow
                 optimize: bool = False,
    ):
        '''
        states is assumed to be a list that is increasing but never modified
        '''
        self.states = states
        self.predicates = predicates
        self.top_clauses = tuple(top_clauses)
        self.m = len(self.top_clauses)
        # assert self.m > 0
        self.variables = [destruct_clause(self.top_clauses[k])[0] for k in range(self.m)]
        self.literals = [destruct_clause(self.top_clauses[k])[1] for k in range(self.m)]
        self.n = [len(self.literals[k]) for k in range(self.m)]
        self.all_n = [set(range(self.n[k])) for k in range(self.m)]  # used in complement fairly frequently
        self.optimize = optimize
        self.solver = z3.Optimize() if optimize else z3.Solver()  # type: ignore # TODO - fix typing
        self.lit_vs = [[z3.Bool(f'lit_{k}_{i}') for i in range(self.n[k])] for k in range(self.m)]
        self.state_vs: List[List[z3.ExprRef]] = [[] for k in range(self.m)]
        self.predicate_vs: List[List[z3.ExprRef]] = [[] for k in range(self.m)]

    def _new_states(self) -> None:
        if self.m == 0:
            return
        new = range(len(self.state_vs[0]), len(self.states))
        if len(new) == 0:
            return
        for k in range(self.m):
            self.state_vs[k].extend(z3.Bool(f's_{k}_{i}') for i in new)
            print(f'Mapping out subclauses-state interaction with {len(new)} new states for {self.to_clause(k, self.all_n[k])}')
            total_mus = 0
            total_mss = 0
            results = multiprocessing_map_clause_state_interaction([
                (self.variables[k], self.literals[k], self.states[i])
                for i in new
            ])
            for i in new:
                all_mus, all_mss = results.pop(0)
                assert len(all_mus) == 0
                # use only all_mss
                self.solver.add(self.state_vs[k][i] == z3.And(*(
                    z3.Or(*(
                        self.lit_vs[k][j] for j in sorted(self.all_n[k] - v)
                    ))
                    for v in all_mss
                )))
                total_mus += len(all_mus)
                total_mss += len(all_mss)
            print(f'Done subclauses-states (total_cdnf={total_mus + total_mss}, total_mus={total_mus}, total_mss={total_mss})')

    def _new_predicates(self) -> None:
        if self.m == 0:
            return
        new = range(len(self.predicate_vs[0]), len(self.predicates))
        if len(new) == 0:
            return
        for k in range(self.m):
            self.predicate_vs[k].extend(z3.Bool(f'p_{k}_{i}') for i in new)
            print(f'Mapping out subclauses-predicate interaction with {len(new)} new predicates for {self.to_clause(k, self.all_n[k])}')
            total_mus = 0
            total_mss = 0
            results = multiprocessing_map_clause_state_interaction([
                (self.variables[k], self.literals[k], self.predicates[i])
                for i in new
            ])
            for i in new:
                all_mus, all_mss = results.pop(0)
                assert len(all_mus) == 0
                # use only all_mss
                self.solver.add(z3.Or(z3.Not(self.predicate_vs[k][i]), *(
                    z3.And(*(
                        z3.Not(self.lit_vs[k][j]) for j in sorted(self.all_n[k] - v)
                    ))
                    for v in all_mss
                )))
                total_mus += len(all_mus)
                total_mss += len(all_mss)
            print(f'Done subclauses-predicates (total_cdnf={total_mus + total_mss}, total_mus={total_mus}, total_mss={total_mss})')

    def separate(self,
                 pos: Collection[int] = (),
                 neg: Collection[int] = (),
                 imp: Collection[Tuple[int, int]] = (),
                 ps: Collection[int] = (),
                 soft_pos: Collection[int] = (),
                 soft_neg: Collection[int] = (),
                 soft_imp: Collection[Tuple[int, int]] = (),
                 soft_ps: Collection[int] = (),
    ) -> Optional[List[FrozenSet[int]]]:
        '''
        find a conjunction of subclauses that respects given constraints, and optionally as many soft constraints as possible

        TODO: to we need an unsat core in case there is no subclause?

        NOTE: the result must contain a subclause of each top clause, i.e., true cannot be used instead of one of the top clauses
        '''
        self._new_states()
        self._new_predicates()
        assert all(0 <= i < len(self.states) for i in chain(pos, neg, soft_pos, soft_neg))
        assert all(0 <= i < len(self.predicates) for i in chain(ps, soft_ps))
        sep = list(chain(
            (z3.And(*(self.state_vs[k][i] for k in range(self.m))) for i in sorted(pos)),
            (z3.Or(*(z3.Not(self.state_vs[k][i]) for k in range(self.m))) for i in sorted(neg)),
            (z3.Implies(
                z3.And(*(self.state_vs[k][i] for k in range(self.m))),
                z3.And(*(self.state_vs[k][j] for k in range(self.m))),
            ) for i, j in sorted(imp)),
            (self.predicate_vs[i] for i in sorted(ps)),
        ))
        soft = list(chain(
            (z3.And(*(self.state_vs[k][i] for k in range(self.m))) for i in sorted(soft_pos)),
            (z3.Or(*(z3.Not(self.state_vs[k][i]) for k in range(self.m))) for i in sorted(soft_neg)),
            (z3.Implies(
                z3.And(*(self.state_vs[k][i] for k in range(self.m))),
                z3.And(*(self.state_vs[k][j] for k in range(self.m))),
            ) for i, j in sorted(soft_imp)),
            (self.predicate_vs[i] for i in sorted(soft_ps)),
        ))
        self.solver.push()
        for c in sep:
            self.solver.add(c)
        if len(soft) > 0:
            assert self.optimize
            for c in soft:
                self.solver.add_soft(c)
        if self.optimize:
            # optimize for smaller clauses
            for v in chain(*self.lit_vs):
                self.solver.add_soft(z3.Not(v))
        print(f'Checking MultiSubclausesMapICE.solver... ', end='')
        res = self.solver.check()
        print(res)
        assert res in (z3.unsat, z3.sat)
        if res == z3.unsat:
            self.solver.pop()
            return None
        # minimize for strongest possible clause
        # TODO: just use z3's Optimize instead of minimizing manually
        model = self.solver.model()
        forced_to_false = [set(
            i for i, v in enumerate(self.lit_vs[k])
            if not z3.is_true(model[v])
        ) for k in range(self.m)]
        for k in range(self.m):
            for i in range(self.n[k]):
                if i not in forced_to_false[k]:
                    ki = [(kk, ii) for kk in range(self.m) for ii in forced_to_false[kk]] + [(k, i)]
                    print(f'Checking MultiSubclausesMapICE.solver... ', end='')
                    res = self.solver.check(*(z3.Not(self.lit_vs[kk][ii]) for kk, ii in sorted(ki)))
                    print(res)
                    assert res in (z3.unsat, z3.sat)
                    if res == z3.sat:
                        forced_to_false[k].add(i)
        ki = [(kk, ii) for kk in range(self.m) for ii in forced_to_false[kk]]
        assert self.solver.check(*(z3.Not(self.lit_vs[kk][ii]) for kk, ii in sorted(ki))) == z3.sat
        result = [frozenset(self.all_n[k] - forced_to_false[k]) for k in range(self.m)]
        self.solver.pop()
        return result

    def to_clause(self, k: int, s: Iterable[int]) -> Expr:
        lits = [self.literals[k][i] for i in sorted(s)]
        free = set(chain(*(lit.free_ids() for lit in lits)))
        vs = [v for v in self.variables[k] if v.name in free]
        return Forall(vs, Or(*lits)) if len(vs) > 0 else Or(*lits)



def forward_explore_marco_turbo(solver: Solver,
                                clauses: Sequence[Expr],
                                _states: Optional[Iterable[State]] = None
) -> Tuple[List[State], Sequence[Expr]]:

    prog = syntax.the_program
    # inits = tuple(init.expr for init in prog.inits())
    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # must be in CNF for use in eval_in_state

    states: List[State] = [] if _states is None else list(_states)
    predicates: List[Expr] = []  # growing list of predicates considered
    live: FrozenSet[int] = frozenset()  # indices into predicates for predicates p s.t. init U states |= p /\ wp(p)

    def alpha_live(states: Collection[State]) -> Sequence[Expr]:
        return alpha_from_predicates(solver, states, [predicates[i] for i in sorted(live)])

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

    def wp_valid(clause: Expr) -> bool:
        # return True iff wp(clause) is implied by init and valid in all states
        # when returning False, add a new transition to states
        assert valid(clause)
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

    maps = [SubclausesMapTurbo(top_clause, states, predicates) for top_clause in clauses]


    rotate = 0
    # for rotate in itertools.count(0):
    while True:
        assert all(valid(predicates[i]) and wp_valid(predicates[i]) for i in live)

        for i in range(len(maps)):
            ii = (rotate + i) % len(maps)
            mp = maps[ii]
            while True:
                print(f'Trying maps[{ii}]')
                seed = mp.separate(frozenset(range(len(states))), frozenset(), live)
                if seed is not None:
                    clause = mp.to_clause(seed)
                    print(f'Potential predicate is: {clause}')
                    s = check_initial(solver, clause)
                    if s is not None:
                        states.append(s)
                    else:
                        break
                else:
                    print(f'maps[{ii}] is covered')
                    break
            if seed is not None:
                rotate = ii # so next time we start here
                break
        else:
            # here init U states |= live /\ wp(live), and also there is no uncharted territory in the maps
            live_predicates = [predicates[i] for i in sorted(live)]
            assert live_predicates == dedup_equivalent_predicates(solver, live_predicates)
            return states, live_predicates

        n_states = len(states)
        assert valid(clause)
        if wp_valid(clause):
            # the clause is valid, and its wp is also valid
            assert len(states) == n_states
            live = live | {len(predicates)}
            predicates.append(clause)
            print(f'Potential predicate is wp_valid: {clause}')
        else:
            assert len(states) > n_states
            print(f'Potential predicate is not wp_valid: {clause}')
            # the clause was valid, but its wp was not. we already learned a new state so now it's not even valid
            # we no do forward_explore with the live predicates to see which ones are left
            print(f'Starting forward_explore')
            _states, a, _, _ = forward_explore(solver, alpha_live, states)
            print(f'Finished forward_explore, found {len(_states) - len(states)} new states and killed {len(live) - len(a)} predicates')
            assert states == _states[:len(states)]
            states.extend(_states[len(states):])
            assert states == _states
            live = frozenset(
                i for i in live
                if predicates[i] in a
            )
    assert False


def forward_explore_marco(solver: Solver,
                          clauses: Sequence[Expr],
                          _states: Optional[Iterable[State]] = None
) -> Tuple[List[State], Sequence[Expr]]:

    prog = syntax.the_program
    states: List[State] = [] if _states is None else list(_states)

    # inits = tuple(init.expr for init in prog.inits())
    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # must be in CNF for use in eval_in_state

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
    # inits = tuple(init.expr for init in prog.inits())
    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # must be in CNF for use in eval_in_state
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
        if changes:
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
            if x == y:# or cheap_check_implication([], [Iff(x, y)]):
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
    # safety = tuple(inv.expr for inv in prog.invs() if inv.is_safety)
    safety = tuple(chain(*(as_clauses(inv.expr) for inv in prog.invs() if inv.is_safety))) # must be in CNF for use in eval_in_state
    reachable_states : List[State] = []

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
    def forward_explore_clauses(states: Iterable[State]) -> Tuple[List[State], Sequence[Expr]]:
        # TODO: maybe this should be controlled by command line argument
        # return forward_explore(s, alpha_clauses, states)[:2]
        # return forward_explore_marco(s, clauses, states)
        return forward_explore_marco_turbo(s, clauses, states)

    while True:
        reachable_states, a = forward_explore_clauses(reachable_states)
        print(f'[{datetime.now()}] Current reachable states ({len(reachable_states)}):')
        for m in reachable_states:
            print(str(m) + '\n' + '-'*80)
        if not cheap_check_implication(a, safety):
            print('Found safety violation!')
            dump_caches()
            return 'UNSAFE'
        sharp_predicates = tuple(a)
        print(f'[{datetime.now()}] Current sharp predicates ({len(sharp_predicates)}):')
        for p in sharp_predicates:
            print(f'  {p}')
        states = list(reachable_states)
        unreachable = []
        while True:
            for p in a:
                res = check_two_state_implication(s, a, p, 'CTI')
                if res is not None:
                    prestate, poststate = res
                    unreachable.append(prestate)
                    states.extend([prestate, poststate]) # so that forward_explore also considers extensions of the prestate
                    if sharp:
                        states, a, _, _ = forward_explore(s, alpha_sharp, states)
                    else:
                        states, a = forward_explore_clauses(states)
                    break
            else:
                break
        print(f'[{datetime.now()}] Current inductive invariant ({len(a)} predicates) is:' if len(a) > 0 else '[{datetime.now()}] Current inductive invariant is true')
        for p in sorted(a, key=lambda x: len(str(x))):
            print(p)
        if len(a) > 0 and cheap_check_implication(a, safety):
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

def repeated_houdini_bounds(solver: Solver) -> str:
    '''
    A more primal-dual repeated houdini with bounds and cleanups (sharp only for now)
    '''
    prog = syntax.the_program
    global cache_path
    cache_path = Path(utils.args.filename).with_suffix('.cache')
    load_caches()

    # safety = tuple(inv.expr for inv in prog.invs() if inv.is_safety)
    safety = tuple(chain(*(as_clauses(inv.expr) for inv in prog.invs() if inv.is_safety))) # must be in CNF for use in eval_in_state
    # inits = tuple(init.expr for init in prog.inits())
    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # must be in CNF for use in eval_in_state
    assert cheap_check_implication(inits, safety), 'Initial states not safe'

    states: List[State] = []
    maps: List[SubclausesMapTurbo] = []  # for each state, a map with the negation of its diagram
    # the following are indices into states:
    reachable: FrozenSet[int] = frozenset()
    live_states: FrozenSet[int] = frozenset() # not yet ruled out by invariant
    transitions: List[Tuple[int, int]] = [] # TODO: maybe should be frozenset
    substructure: List[Tuple[int, int]] = [] # TODO: maybe should be frozenset
    ctis: FrozenSet[int] = frozenset()  # states that are "roots" of forward reachability trees that came from top-level Houdini
    covered: FrozenSet[int] = frozenset()  # we found all sharp predicates that rule out this state
    bmced: FrozenSet[int] = frozenset() # we have already used BMC to check that this state is not reachable from init in 5 steps (will be made more general later)
    score: Dict[int,float] = defaultdict(float)

    def add_state(s: State) -> int:
        nonlocal live_states
        assert all(eval_in_state(None, s, predicates[j]) for j in sorted(inductive_invariant))
        if s in states:
            # assert False
            return states.index(s)
        i = len(states)
        states.append(s)
        predicates_of_state.append([])
        sharp_predicates_of_state.append(frozenset())
        live_states |= {i}
        for j in range(i):
            t = states[j]
            if is_substructure(s, t):
                substructure.append((j, i))
            if is_substructure(t, s):
                substructure.append((i, j))
        cs = as_clauses(Not(s.as_diagram(0).to_ast()))
        assert len(cs) == 1
        c = cs[0]
        maps.append(SubclausesMapTurbo(c, states, predicates_of_state[i], True))
        return i

    predicates: List[Predicate] = []
    sharp_predicates: FrozenSet[int] = frozenset()   # indices into predicates for predicates for current set of sharp predicates
    inductive_invariant: FrozenSet[int] = frozenset()  # indices into predicates for current inductive invariant
    frames: List[List[Predicate]] = []

    #ctis_of_predicate: List[List[FrozenSet[int]]] = [] # ctis_of_predicate[i] is a list of sets of CTIs (indices into states). For each i and n, ctis_of_predicate[i][:n] show how why predicates[i] does not have an inductive invariant with n predicates. Once all ctis in ctis_of_predicate[i][:-1] are covered, then it can be extened, and the bound is increased
    predicates_of_state: List[List[Predicate]] = [] # for every state, list of predicates ruling out this state, which grows until the state is covered
    sharp_predicates_of_state: List[FrozenSet[int]] = [] # for every state, set of indices into predicates_of_state[i] that are still sharp

    for p in safety:
        i = len(predicates)
        predicates.append(p)
        # ctis_of_predicate.append([])
        sharp_predicates |= {i}

    def alpha_sharp(states: Collection[State]) -> Sequence[Expr]:
        return sorted(
            alpha_from_predicates(
                solver,
                states,
                [predicates[i] for i in sorted(sharp_predicates)],
            ),
            key=lambda x: (len(str(x)),str(x))
        )

    def close_forward(s: FrozenSet[int]) -> FrozenSet[int]:
        '''
        return closure under *abstract* post, also adds all known reachable states.
        abstract post meanst we consider an abstract transition from s to t if t is a substructure of s.
        '''
        r = s | frozenset(reachable)
        changes = True
        while changes:
            changes = False
            # close under transitions and substructure
            for i, j in chain(transitions, substructure):
                if i in r and j not in r:
                    r |= {j}
                    changes = True
        return r

    def forward_explore_from_state(src: Optional[int],
                                   # k: int
    ) -> None:
        # forward explore (concretley) either from the initial states
        # or from states[src], according to the current sharp predicates,
        # using unrolling of k

        # NOTE: this finds new reachable states, presumably only if i
        # is None assuming that forward_explore_from_state(None) was
        # called before with the same predicates

        nonlocal reachable
        r: FrozenSet[int] = reachable
        if src is not None:
            r |= {src}
        r = close_forward(r)
        a = list(chain(
            ## (maps[k].to_clause(maps[k].all_n) for k in sorted(live_states - r)), # to try to connect to existing states or their superstructures
            (predicates[j] for j in sorted(sharp_predicates)),
        ))
        def alpha_a(states: Collection[State]) -> Sequence[Expr]:
            return alpha_from_predicates(solver, states, a)
        n = -1
        while len(r) > n:
            n = len(r)
            r = close_forward(r)
            _states, _a, _initials, _transitions = forward_explore(
                # TODO: this does not connect already discovered states
                # TODO: use unrolling
                solver,
                alpha_a,
                [states[i] for i in sorted(r)],
            )
            a = list(_a)
            assert _states[:len(r)] == [states[i] for i in sorted(r)]
            index_map: Dict[int, int] = dict()
            for i in range(len(_states)):
                try:
                    index_map[i] = states.index(_states[i])
                except ValueError:
                    index_map[i] = add_state(_states[i])
            assert [index_map[i] for i in range(len(r))] == sorted(r)
            n_reachable = len(reachable)
            reachable |= set(index_map[i] for i in _initials)
            for i, j in _transitions:
                ii, jj = index_map[i], index_map[j]
                transitions.append((ii, jj))
            reachable = close_forward(reachable)
            assert src is None or len(reachable) == n_reachable
            r = close_forward(r)
            assert frozenset(index_map.values()) <= r
        # return a

    def houdini() -> None:
        '''Check if any subset of the sharp predicates is inductive, and possibly add new ctis

        NOTE: This may actually find new reachable states even after
        forward_explore_from_state(None) ran, since we may find a CTI
        and then discover that the prestate is reachable all at
        once. Maybe this should be changed to be more consistent by
        treating negations of diagrams as predicates and not as a
        special case

        '''
        nonlocal ctis
        nonlocal reachable
        nonlocal inductive_invariant
        p_cti = None
        a = [predicates[i] for i in sorted(sharp_predicates)]
        r = reachable
        assert all(eval_in_state(None, states[i], p) for i, p in product(sorted(reachable), a))
        p_cti = None
        while True:
            r = close_forward(r)
            a = [p for p in a if all(eval_in_state(None, states[i], p) for i in sorted(r))]
            if len(a) == 0:
                break
            changes = False
            for i in sorted(ctis - r):
                if all(eval_in_state(None, states[i], p) for p in a):
                    r |= {i}
                    changes = True
            if changes:
                continue
            for i in sorted(ctis - r):
                res = check_two_state_implication(
                    solver,
                    a,
                    maps[i].to_clause(maps[i].all_n),
                    f'backward-transition from states[{i}]'
                )
                if res is not None:
                    prestate, poststate = res
                    i_pre = add_state(prestate)
                    i_post = add_state(poststate)
                    transitions.append((i_pre, i_post))
                    assert i_post == i or (i_post, i) in substructure
                    ctis |= {i_pre} # TODO: rethink this?
                    r |= {i_pre}
                    changes = True
                    break # TODO: not sure we should break here, for now we do, like in the next loop
            if changes:
                continue
            assert p_cti not in a, f'Predicate for which we added a CTI was not eliminated: {p_cti}'
            print(f'\nChecking for new disconnected CTIs')
            # TODO: this maybe this should be biased toward
            # finding prestates or poststates of existing states
            # (right now it is not even really biased toward using
            # existing transitions)
            for p in a:
                res = check_two_state_implication(solver, a, p, 'CTI')
                if res is not None:
                    prestate, poststate = res
                    i_pre = add_state(prestate)
                    i_post = add_state(poststate)
                    transitions.append((i_pre, i_post))
                    ctis |= {i_pre}
                    ## forward_explore_from_state(None) # we could have learned that i_pre is reachable here....
                    forward_explore_from_state(i_pre)
                    p_cti = p
                    break
            else:
                print(f'No disconnected CTIs found')
                break
        # here, a is inductive (but it may not imply safety)
        inv = frozenset(predicates.index(p) for p in a)
        assert inductive_invariant <= inv
        inductive_invariant = inv

    def houdini_frames() -> None:
        '''Check if any subset of the sharp predicates is inductive, and
        possibly add new ctis. This version is stratified, and
        computes "frames" similar to IC3, but since multi-transition
        CTIs are used they have a slightly different meaning.

        NOTE: This may actually find new reachable states even after
        forward_explore_from_state(None) ran, since we may find a CTI
        and then discover that the prestate is reachable all at
        once. Maybe this should be changed to be more consistent by
        treating negations of diagrams as predicates and not as a
        special case

        '''
        nonlocal ctis
        nonlocal reachable
        nonlocal inductive_invariant
        nonlocal frames
        assert_invariants()
        frames = [[predicates[i] for i in sorted(sharp_predicates)]]
        r = reachable
        while True:
            assert r == close_forward(r)
            a = frames[-1]
            assert all(eval_in_state(None, states[i], p) for i, p in product(sorted(r), a))
            for i in sorted(ctis):  # TODO: ctis or live_states?
                if i not in r and all(eval_in_state(None, states[i], p) for p in a):
                    r |= {i}
                    r = close_forward(r)
            for i in sorted(ctis):  # TODO: ctis or live_states?
                if i in r:
                    continue
                res = check_two_state_implication(
                    solver,
                    a,
                    maps[i].to_clause(maps[i].all_n),
                    f'backward-transition from states[{i}]'
                )
                if res is not None:
                    prestate, poststate = res
                    i_pre = add_state(prestate)
                    i_post = add_state(poststate)
                    transitions.append((i_pre, i_post))
                    assert i_post == i or (i_post, i) in substructure
                    ctis |= {i_pre} # TODO: rethink this?
                    forward_explore_from_state(None) # we could have learned that i_pre is reachable here.... TODO: this is inconsistent with frames, and this should be fixed
                    forward_explore_from_state(i_pre)
                    r |= {i_pre}
                    r = close_forward(r)
            b = [p for p in a if all(eval_in_state(None, states[i], p) for i in sorted(r))]
            for p in b[:]:
                if p not in b:
                    continue
                res = check_two_state_implication(solver, a, p, 'CTI')
                if res is not None:
                    prestate, poststate = res
                    i_pre = add_state(prestate)
                    i_post = add_state(poststate)
                    transitions.append((i_pre, i_post))
                    ctis |= {i_pre}
                    forward_explore_from_state(None) # we could have learned that i_pre is reachable here.... TODO: this is inconsistent with frames, and this should be fixed
                    forward_explore_from_state(i_pre)
                    r |= {i_pre}
                    r = close_forward(r)
                    b = [p for p in b if all(eval_in_state(None, states[i], p) for i in sorted(r))]
            if a == b:
                break
            else:
                frames.append(b)
        # here, frames[-1] is inductive (but it may not imply safety)
        assert frames[-1] == a == b
        inv = frozenset(predicates.index(p) for p in a)
        assert inductive_invariant <= inv
        inductive_invariant = inv

    def houdini_with_existing(ps: FrozenSet[int]) -> FrozenSet[int]:
        '''
        return a subset of ctis that show why no subset of given predicates is inductive
        '''
        a = [predicates[i] for i in ps]
        r = reachable
        assert all(eval_in_state(None, states[i], p) for i, p in product(sorted(reachable), a))
        result: FrozenSet[int] = frozenset()
        while True:
            r = close_forward(r)
            a = [p for p in a if all(eval_in_state(None, states[i], p) for i in sorted(r))]
            for i in sorted(ctis - r):
                # note: we bias toward earlier discovered ctis TODO:
                # minimize the set instead, or bias toward covered
                # ones, or explore all of them
                if (    all(eval_in_state(None, states[i], p) for p in a) and
                    not all(eval_in_state(None, states[j], p) for j, p in product(sorted(close_forward(frozenset([i]))), a))):
                    r |= {i}
                    result |= {i}
                    break
            else:
                assert len(a) ==0
                break
        return result

    def new_reachable_states() -> None:
        nonlocal sharp_predicates
        nonlocal sharp_predicates_of_state
        nonlocal covered
        sharp_predicates = frozenset(
            j for j in sorted(sharp_predicates)
            if all(eval_in_state(None, states[k], predicates[j])
                   for k in sorted(reachable)
            )
        )
        for i in range(len(states)):
            n = len(sharp_predicates_of_state[i])
            sharp_predicates_of_state[i] = frozenset(
                j for j, p in enumerate(predicates_of_state[i])
                if all(eval_in_state(None, states[k], p)
                       for k in sorted(reachable)
                )
            )
            if len(sharp_predicates_of_state[i]) < n:
                covered -= {i}
        # TODO: as the code above demonstrates, it would be better to keep the connection between predicates and predicates_of_state

    def assert_invariants() -> None:
        # for debugging
        assert reachable == close_forward(reachable)
        assert sharp_predicates <= frozenset(
            j for j, p in enumerate(predicates)
            if all(eval_in_state(None, states[k], p)
                   for k in sorted(reachable)
            )
        )
        for i in range(len(states)):
            assert sharp_predicates_of_state[i] == frozenset(
                j for j, p in enumerate(predicates_of_state[i])
                if all(eval_in_state(None, states[k], p)
                       for k in sorted(reachable)
                )
            )
        assert live_states == frozenset(
            i for i, s in enumerate(states)
            if all(eval_in_state(None, s, predicates[j])
                   for j in sorted(inductive_invariant)
            )
        )


    while True:
        # assert_invariants() -- not true because of BMC, TODO rethink this
        n_reachable = len(reachable)
        list(map(forward_explore_from_state, chain([None], ctis))) # TODO: parallel?, TODO: can be more frugal here and compute less
        if len(reachable) > n_reachable:
            print(f'Forward explore found {len(reachable) - n_reachable} new reachable states')
            new_reachable_states()
        assert_invariants()

        # Houdini, to check if anything new is inductive, adding new
        # ctis, which will be used later when computing bounds
        assert_invariants()
        n_inductive_invariant = len(inductive_invariant)
        n_reachable = len(reachable)
        # houdini()
        houdini_frames()
        if len(reachable) > n_reachable:
            # this can happen since we may have some ctis without any predicate excluding them, and we do have backward transitions
            # assert False
            print(f'Houdini found {len(reachable) - n_reachable} new reachable states')
            new_reachable_states()
        if len(inductive_invariant) > n_inductive_invariant:
            # TODO - reset all kinds of bounds, unrefince, etc
            print(f'Houdini found {len(inductive_invariant) - n_inductive_invariant} new inductive predicates')
            live_states = frozenset(
                i for i, s in enumerate(states)
                if all(eval_in_state(None, s, predicates[j])
                       for j in sorted(inductive_invariant)
                )
            )
            ctis = ctis & live_states
            # keep only predicates used to rule out live states, TODO: not sure if this is good or bad
            live_predicates = set(
                predicates_of_state[i][j]
                for i in sorted(live_states)
                for j in sharp_predicates_of_state[i]
            ) | set(safety)
            n_sharp_predicates = len(sharp_predicates)
            sharp_predicates = inductive_invariant | frozenset(
                j for j in sharp_predicates
                if predicates[j] in live_predicates
            )
            print(f'Unrefined {n_sharp_predicates - len(sharp_predicates)} predicates')

        assert_invariants()

        # print status and possibly terminate
        print(f'\n[{datetime.now()}] Current live states ({len(live_states)} total, {len(reachable)} reachable, {len(ctis)} ctis, {len(covered)} covered):\n' + '-' * 80)
        for i in sorted(live_states):
            notes: List[str] = []
            if i in reachable:
                notes.append('reachable')
            notes.append('covered' if i in covered else 'uncovered')
            if i in ctis:
                notes.append('cti')
            note = '(' + ', '.join(notes) + ')'
            print(f'states[{i:3}]{note}:\n{states[i]}\n' + '-' * 80)
        for i in reachable:
            if not cheap_check_implication([states[i].as_onestate_formula(0)], safety):
                print(f'\nFound safety violation by reachable state (states[{i}]).')
                dump_caches()
                return 'UNSAFE'
        print(f'\n[{datetime.now()}] Current sharp predicates ({len(sharp_predicates)} total, {len(inductive_invariant)} proven):')
        for i in sorted(sharp_predicates):
            max_frame = max(j for j, f in enumerate(frames) if predicates[i] in f)
            assert max_frame < len(frames) - 1 or i in inductive_invariant
            note = (' (invariant)' if i in inductive_invariant else f' ({max_frame + 1})')
            print(f'  predicates[{i:3}]{note}: {predicates[i]}')
        if len(inductive_invariant) > 0 and cheap_check_implication([predicates[i] for i in sorted(inductive_invariant)], safety):
            print('Proved safety!')
            dump_caches()
            return 'SAFE'

        # compute bounds for each predicate
        bounds: Dict[int, int] = dict()  # mapping from predicate index to its bound
        still_uncovered: Dict[int, FrozenSet[int]] = dict()  # mapping from predicate index to set of uncovered states that prevent increasing its bound
        for i in sorted(sharp_predicates - inductive_invariant):
            assert_invariants()
            if all(eval_in_state(None, states[j], predicates[i]) for j in sorted(live_states)):
                # TODO: revisit this
                bounds[i] = 0
                still_uncovered[i] = frozenset()
                continue
            ctis_so_far: FrozenSet[int] = frozenset()
            ps = frozenset([i])
            n = 0
            while True:
                assert n < 100
                assert ctis_so_far <= covered
                new_ctis = houdini_with_existing(ps) # TODO: we don't need to reach all the way to TOP, can stop at {i}, or maybe lower
                n += 1
                if new_ctis <= ctis_so_far:
                    assert False
                ctis_so_far |= new_ctis
                assert len(ctis_so_far & reachable) == 0
                assert ctis_so_far <= live_states
                if new_ctis <= covered:
                    for j in new_ctis:
                        ps |= frozenset(predicates.index(predicates_of_state[j][k]) for k in sharp_predicates_of_state[j])
                else:
                    still_uncovered[i] = new_ctis - covered
                    bounds[i] = n
                    break

        print(f'\n[{datetime.now()}] Current bounds:')
        for i in sorted(sharp_predicates - inductive_invariant):
            print(f'  predicates[{i:3}]: bound is {bounds[i]}, uncovered: {sorted(still_uncovered[i])}, predicate is: {predicates[i]}')
        print()

        # select a state with "high score"
        for k in score:
            score[k] = 0  # TODO: explore other decay, i.e., *= 0.9
        min_bound = min(x for x in bounds.values() if x > 0)
        candidates: Set[int] = set()
        for i in sorted(sharp_predicates - inductive_invariant):
            if bounds[i] == min_bound:
                for j in still_uncovered[i]:
                    assert j not in reachable and j in live_states
                    score[j] += 1
                    candidates.add(j)
        print(f'\n[{datetime.now()}] Current scores:')
        for i in sorted(candidates):
            assert i not in covered
            assert score[i] > 0
            print(f'  states[{i}]: score={score[i]:.2e}, sharp_predicates={len(sharp_predicates_of_state[i])}, total_predicates={len(predicates_of_state[i])}')

        f = lambda i: score[i] # - len(sharp_predicates_of_state[i])
        max_score = max(map(f, candidates))
        ii = min(i for i in candidates if f(i) == max_score)
        print(f'Selected states[{ii}] for refinement\n')

        if ii not in bmced:
            print(f'Trying to reach states[{ii}] in up to 5 steps')
            p = maps[ii].to_clause(maps[ii].all_n)
            changes = False
            for k in range(1, 6):
                print(f'Checking if init satisfies WP_{k} of ~states[{ii}]... ',end='')
                res = check_k_state_implication(solver, inits, p, k)
                if res is not None:
                    prestate, *poststates = res
                    # add all states, including first one that is an initial state
                    # add new initial state
                    i_pre = add_state(prestate)
                    reachable |= {i_pre}
                    for poststate in poststates:
                        i_post = add_state(poststate)
                        transitions.append((i_pre, i_post))
                        # reachable |= {i_post} # not doing this to trigger discovery of new reachable states on the next loop iteration
                        i_pre = i_post
                    changes = True
                    break
                else:
                    print('YES')
            if changes:
                print(f'Managed to reach states[{ii}], looping\n')
                continue
            else:
                bmced |= {ii}

        mp = maps[ii]
        while True:
            seed = mp.separate(
                pos=reachable,
                neg=frozenset(),
                ps=sharp_predicates_of_state[ii],
                soft_neg=frozenset(candidates),
            )
            if seed is not None:
                clause = mp.to_clause(seed)
                print(f'Potential predicate is: {clause}')
                s = check_initial(solver, clause)
                if s is not None:
                    print(f'This predicate is not initial, learned a new initial state')
                    # assert s not in states # TODO: this can be violated by a backward transition finding an initial state, and should be fixed by a better forward_explore
                    i = add_state(s)
                    reachable |= {i}
                else:
                    k = len(predicates_of_state[ii])
                    predicates_of_state[ii].append(clause)
                    sharp_predicates_of_state[ii] |= {k}
                    if clause in predicates:
                        if predicates.index(clause) in sharp_predicates:
                            print(f'Already have this predicate, looping\n')
                        else:
                            print(f'Learned previous predicate, looping\n')
                            sharp_predicates |= {predicates.index(clause)}
                    else:
                        print(f'Learned new predicate, looping\n')
                        j = len(predicates)
                        predicates.append(clause)
                        sharp_predicates |= {j}
                    break
            else:
                print(f'maps[{ii}] is covered, looping\n')
                covered |= {ii}
                score[ii] = 0
                break


def cdcl_state_bounds(solver: Solver) -> str:
    '''
    Another attempt at CDCL with bounds (not sharp)
    '''
    prog = syntax.the_program
    global cache_path
    cache_path = Path(utils.args.filename).with_suffix('.cache')
    load_caches()

    print(f'\nStarting cdcl_state_bounds, PID={os.getpid()} [{datetime.now()}]\n')

    # safety = tuple(inv.expr for inv in prog.invs() if inv.is_safety)
    safety = tuple(chain(*(as_clauses(inv.expr) for inv in prog.invs() if inv.is_safety))) # must be in CNF for use in eval_in_state
    # inits = tuple(init.expr for init in prog.inits())
    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # must be in CNF for use in eval_in_state
    assert cheap_check_implication(inits, safety), 'Initial states not safe'

    states: List[State] = []
    maps: List[SubclausesMapTurbo] = []  # for each state, a map with the negation of its diagram
    # the following are indices into states:
    reachable: FrozenSet[int] = frozenset()
    live_states: FrozenSet[int] = frozenset() # not yet ruled out by invariant
    transitions: List[Tuple[int, int]] = [] # TODO: maybe should be frozenset
    substructure: List[Tuple[int, int]] = [] # TODO: maybe should be frozenset
    ctis: FrozenSet[int] = frozenset()  # states that are "roots" of forward reachability trees that came from top-level Houdini
    current_ctis: FrozenSet[int] = frozenset()  # states were used in the last Houdini run
    bmced: FrozenSet[int] = frozenset() # we have already used BMC to check that this state is not reachable from init in 2 steps (will be made more general later)
    state_bounds: Dict[int, int] = defaultdict(int)  # mapping from state index to its bound

    def add_state(s: State) -> int:
        nonlocal live_states
        assert all(eval_in_state(None, s, predicates[j]) for j in sorted(inductive_invariant))
        if s not in states:
            i = len(states)
            print(f'add_state: adding new state: states[{i}]')
            states.append(s)
            live_states |= {i}
            for j in range(i):
                t = states[j]
                if is_substructure(s, t):
                    substructure.append((j, i))
                if is_substructure(t, s):
                    substructure.append((i, j))
            cs = as_clauses(Not(s.as_diagram(0).to_ast()))
            assert len(cs) == 1
            c = cs[0]
            maps.append(SubclausesMapTurbo(c, states, [], True))
            return i
        else:
            i = states.index(s)
            if i not in live_states:
                print(f'add_state: reviving previous state: states[{i}]')
                live_states |= {i}
            return  i

    predicates: List[Predicate] = []
    inductive_invariant: FrozenSet[int] = frozenset()  # indices into predicates for current inductive invariant
    sharp_predicates: FrozenSet[int] = frozenset()  # TODO: change name, not necessarily sharp
    frames: List[List[Predicate]] = []
    step_frames: List[List[Predicate]] = []
    reason_for_predicate: Dict[int, FrozenSet[int]] = defaultdict(frozenset) # for each predicate index, the indices of the states it helps to exclude

    def add_predicate(p: Predicate, reason: Optional[int] = None) -> int:
        nonlocal predicates
        nonlocal sharp_predicates
        nonlocal reason_for_predicate
        if p not in predicates:
            print(f'add_predicate: adding new predicate: {p}')
            j = len(predicates)
            predicates.append(p)
        else:
            j = predicates.index(p)
            if j in sharp_predicates:
                print(f'add_predicate: already have this predicate: {p}')
            else:
                print(f'add_predicate: reviving previous predicate: {p}')
        sharp_predicates |= {j}
        assert all(eval_in_state(None, states[i], p) for i in sorted(reachable))
        if reason is not None:
            reason_for_predicate[j] |= {reason}
        return j

    for p in safety:
        add_predicate(p)

    def alpha_sharp(states: Collection[State]) -> Sequence[Expr]:
        return alpha_from_predicates(
            solver,
            states,
            [predicates[i] for i in sorted(sharp_predicates)],
        )

    def close_forward(s: FrozenSet[int]) -> FrozenSet[int]:
        '''
        return closure under *abstract* post, also adds all known reachable states.
        abstract post meanst we consider an abstract transition from s to t if t is a substructure of s.
        '''
        r = s | frozenset(reachable)
        changes = True
        while changes:
            changes = False
            # close under transitions and substructure
            for i, j in chain(transitions, substructure):
                if i in r and j not in r:
                    r |= {j}
                    changes = True
        return r

    def forward_explore_from_state(src: Optional[int],
                                   # k: int
    ) -> None:
        # forward explore (concretley) either from the initial states
        # or from states[src], according to the current sharp predicates,
        # using unrolling of k

        # NOTE: this finds new reachable states, presumably only if i
        # is None assuming that forward_explore_from_state(None) was
        # called before with the same predicates
        print(f'Starting forward_explore_from_state({src})')

        nonlocal reachable
        r: FrozenSet[int] = reachable
        if src is not None:
            r |= {src}
        r = close_forward(r)
        a = list(chain(
            ## (maps[k].to_clause(maps[k].all_n) for k in sorted(live_states - r)), # to try to connect to existing states or their superstructures
            (predicates[j] for j in sorted(sharp_predicates)),
        ))
        def alpha_a(states: Collection[State]) -> Sequence[Expr]:
            return alpha_from_predicates(solver, states, a)
        n = -1
        while len(r) > n:
            n = len(r)
            r = close_forward(r)
            _states, _a, _initials, _transitions = forward_explore(
                # TODO: this does not connect already discovered states
                # TODO: use unrolling
                solver,
                alpha_a,
                [states[i] for i in sorted(r)],
            )
            a = list(_a)
            assert _states[:len(r)] == [states[i] for i in sorted(r)]
            index_map: Dict[int, int] = dict()
            for i in range(len(_states)):
                try:
                    index_map[i] = states.index(_states[i])
                except ValueError:
                    index_map[i] = add_state(_states[i])
            assert [index_map[i] for i in range(len(r))] == sorted(r)
            n_reachable = len(reachable)
            reachable |= set(index_map[i] for i in _initials)
            for i, j in _transitions:
                ii, jj = index_map[i], index_map[j]
                transitions.append((ii, jj))
            reachable = close_forward(reachable)
            assert src is None or len(reachable) == n_reachable
            r = close_forward(r)
            assert frozenset(index_map.values()) <= r
        print(f'Finished forward_explore_from_state({src})')
        # return a

    def houdini_frames() -> None:
        '''Check if any subset of the sharp predicates is inductive, and
        possibly add new ctis. This version is stratified, and
        computes "frames" similar to IC3, but since multi-transition
        CTIs are used they have a slightly different meaning.

        NOTE: This may actually find new reachable states even after
        forward_explore_from_state(None) ran, since we may find a CTI
        and then discover that the prestate is reachable all at
        once. Maybe this should be changed to be more consistent by
        treating negations of diagrams as predicates and not as a
        special case

        '''
        nonlocal ctis
        nonlocal current_ctis
        nonlocal reachable
        nonlocal inductive_invariant
        nonlocal frames
        assert_invariants()
        frames = [[predicates[i] for i in sorted(sharp_predicates)]]
        r = reachable
        while True:
            assert r == close_forward(r)
            a = frames[-1]
            assert all(eval_in_state(None, states[i], p) for i, p in product(sorted(r), a))
            for i in sorted(ctis):  # TODO: ctis or live_states?
                if (i not in r and
                        all(eval_in_state(None, states[i], p) for p in a) and
                    not all(eval_in_state(None, states[j], p) for j, p in product(sorted(close_forward(frozenset([i]))), a))):
                    r |= {i}
                    r = close_forward(r)
                    current_ctis |= {i}
            for i in sorted(ctis):  # TODO: ctis or live_states?
                if i in r:
                    continue
                print(f'houdini_frames: checking for backward-transition from states[{i}]')
                res = check_two_state_implication(
                    solver,
                    a + [maps[i].to_clause(maps[i].all_n)], # TODO: think about this
                    maps[i].to_clause(maps[i].all_n),
                    f'backward-transition from states[{i}]',
                    # minimize=False, # do not minimize backward-transition - this results in states with too many elements that result in too many instantiations
                )
                print(f'houdini_frames: done checking for backward-transition from states[{i}]')
                if res is not None:
                    prestate, poststate = res
                    i_pre = add_state(prestate)
                    i_post = add_state(poststate)
                    transitions.append((i_pre, i_post))
                    assert i_post == i or (i_post, i) in substructure
                    ctis |= {i_pre} # TODO: rethink this?
                    current_ctis |= {i_pre}
                    forward_explore_from_state(None) # we could have learned that i_pre is reachable here.... TODO: this is inconsistent with frames, and this should be fixed
                    forward_explore_from_state(i_pre)
                    r |= {i_pre}
                    r = close_forward(r)
            b = [p for p in a if all(eval_in_state(None, states[i], p) for i in sorted(r))]
            for p in b[:]:
                if p not in b:
                    continue
                print(f'houdini_frames: checking for CTI to {p}')
                res = check_two_state_implication(solver, a, p, 'CTI')
                print(f'houdini_frames: done checking for CTI to {p}')
                if res is not None:
                    prestate, poststate = res
                    i_pre = add_state(prestate)
                    i_post = add_state(poststate)
                    transitions.append((i_pre, i_post))
                    ctis |= {i_pre}
                    current_ctis |= {i_pre}
                    forward_explore_from_state(None) # we could have learned that i_pre is reachable here.... TODO: this is inconsistent with frames, and this should be fixed
                    forward_explore_from_state(i_pre)
                    r |= {i_pre}
                    r = close_forward(r)
                    b = [p for p in b if all(eval_in_state(None, states[i], p) for i in sorted(r))]
            if a == b:
                break
            else:
                frames.append(b)
        # here, frames[-1] is inductive (but it may not imply safety)
        assert current_ctis <= ctis
        assert frames[-1] == a == b
        inv = frozenset(predicates.index(p) for p in a)
        assert inductive_invariant <= inv
        inductive_invariant = inv

    def compute_step_frames() -> None:
        nonlocal step_frames
        step_frames = [[predicates[i] for i in sorted(sharp_predicates)]]
        while True:
            a = step_frames[-1]

            b = []
            for p in a:
                res = check_two_state_implication(solver, a, p, 'step-CTI')
                if res is not None:
                    prestate, poststate = res
                    # TODO: should we add these states or not? they may not necessarily already be in states
                else:
                    b.append(p)
            if a == b:
                break
            else:
                step_frames.append(b)
        # here, frames[-1] is inductive (but it may not imply safety)
        assert step_frames[-1] == a == b
        inv = frozenset(predicates.index(p) for p in a)
        assert inductive_invariant == inv

    def get_invariant(states_to_exclude: Sequence[int]) -> Tuple[Optional[List[Predicate]], Optional[List[int]]]:
        '''Check if there is an inductive invariant that is a conjunction a
        subclause from the negation of the diagram of states. Either
        return an invariant (list of Predicates) or a list of CTIs.
        '''
        mp = MultiSubclausesMapICE(
            [maps[i].to_clause(maps[i].all_n) for i in states_to_exclude],
            states,
            [],
            False
        )
        def check_sep(s: Collection[int], pos: Collection[int]) -> Optional[List[Predicate]]:
            res = mp.separate(
                pos=sorted(pos),
                imp=[(i, j) for i in sorted(s) for j in sorted(close_forward(frozenset([i])))],
            )
            if res is None:
                return None
            else:
                return [mp.to_clause(k, res[k]) for k in range(mp.m)]
        ctis = live_states - reachable
        res = check_sep(ctis, reachable)
        if res is not None:
            if False:
                # try to include more states, prioratized by step_frames
                # TODO: use z3.Optimize instead of this loop
                # TODO: not sure if this is a good idea
                state_frames = [reachable] + [
                    frozenset(i for i, s in enumerate(states) if all(eval_in_state(None, s, p) for p in a))
                    for a in step_frames
                ]
                for i, pos in enumerate(state_frames):
                    print(f'Trying pos=state_frames[{i}]={sorted(pos)}')
                    _res = check_sep(ctis, pos)
                    if _res is None:
                        print(f'pos=state_frames[{i}] returned None')
                        break
                    else:
                        print(f'pos=state_frames[{i}] returned:')
                        for p in _res:
                            print(f'  {p}')
                        res = _res
                    assert res is not None
            return res, None
        else:
            # minimize ctis
            # TODO: use unsat cores
            for i in sorted(ctis):
                if i in ctis and check_sep(ctis - {i}, reachable) is None:
                    ctis -= {i}
            assert check_sep(ctis, reachable) is None
            return None, sorted(ctis)

    def restart_states_and_predicates() -> None:
        nonlocal sharp_predicates
        nonlocal live_states
        nonlocal ctis
        nonlocal current_ctis
        nonlocal state_bounds
        nonlocal reason_for_predicate
        # keep only inductive invariant and safety
        sharp_predicates = inductive_invariant | frozenset(
            j for j in sharp_predicates
            if predicates[j] in safety
        )
        reason_for_predicate.clear()
        # keep only reachable and backward reachable states
        bad_states = frozenset(
            i for i in sorted(live_states) if
            not all(eval_in_state(None, states[i], p) for p in safety)
        )
        live_states = frozenset(i for i in sorted(live_states) if (
            i in reachable or
            i in bad_states or
            len(close_forward(frozenset([i])) & bad_states) > 0
        ))
        ctis &= live_states
        current_ctis &= live_states
        state_bounds.clear()

    def new_reachable_states() -> None:
        nonlocal sharp_predicates
        nonlocal current_ctis
        nonlocal reachable
        reachable = close_forward(reachable)
        sharp_predicates = frozenset(
            j for j in sorted(sharp_predicates)
            if all(eval_in_state(None, states[k], predicates[j])
                   for k in sorted(reachable)
            )
        )
        current_ctis -= reachable

    def new_inductive_invariants() -> None:
        nonlocal live_states
        nonlocal ctis
        nonlocal sharp_predicates
        nonlocal state_bounds
        live_states = frozenset(
            i for i in sorted(live_states)
            if all(eval_in_state(None, states[i], predicates[j])
                   for j in sorted(inductive_invariant)
            )
        )
        ctis &= live_states
        state_bounds.clear()  # TODO: maybe do something a bit better, i.e., record the set of states explaining the bound, and keep it if they are still live
        for i in reason_for_predicate:
            reason_for_predicate[i] &= live_states

        sharp_predicates = inductive_invariant | frozenset(
            j for j in sharp_predicates
            if len(reason_for_predicate[j]) > 0 or predicates[j] in safety
        )

    def assert_invariants() -> None:
        # for debugging
        assert reachable == close_forward(reachable)
        assert sharp_predicates <= frozenset(
            j for j, p in enumerate(predicates)
            if all(eval_in_state(None, states[k], p)
                   for k in sorted(reachable)
            )
        )
        assert live_states <= frozenset(
            i for i, s in enumerate(states)
            if all(eval_in_state(None, s, predicates[j])
                   for j in sorted(inductive_invariant)
            )
        )
        assert ctis <= live_states
        assert current_ctis <= ctis
        assert len(current_ctis & reachable) == 0
        for i in sorted(sharp_predicates - inductive_invariant):
            assert predicates[i] in safety or len(reason_for_predicate[i]) > 0
        for x in reason_for_predicate.values():
            assert x <= live_states

    while True:
        # assert_invariants() # not true if we have BMC, TODO rethink this
        n_reachable = len(reachable)
        #m = -1
        #while m != len(states):
        #    m = len(states)
        # m = len(states)
        # list(map(backward_explore_from_state, ctis))
        # print(f'Backward explore added {len(states)-m} new states')
        list(map(forward_explore_from_state, chain([None], ctis))) # TODO: parallel?, TODO: can be more frugal here and compute less
        if len(reachable) > n_reachable:
            print(f'Forward explore found {len(reachable) - n_reachable} new reachable states')
            new_reachable_states()
            print(f'Restarting...')
            restart_states_and_predicates()
            continue
        assert_invariants()

        # Houdini, to check if anything new is inductive, adding new
        # ctis, which will be used later when computing bounds
        assert_invariants()
        n_inductive_invariant = len(inductive_invariant)
        n_reachable = len(reachable)
        current_ctis = frozenset()
        houdini_frames()
        compute_step_frames()
        if len(reachable) > n_reachable:
            # this can happen since we may have some ctis without any predicate excluding them, and we do have backward transitions. TODO: figure out something more consistent
            # assert False
            print(f'Houdini found {len(reachable) - n_reachable} new reachable states')
            new_reachable_states()
        if len(inductive_invariant) > n_inductive_invariant:
            print(f'Houdini found {len(inductive_invariant) - n_inductive_invariant} new inductive predicates')
            n_sharp_predicates = len(sharp_predicates)
            new_inductive_invariants()
            print(f'Restarting...')
            restart_states_and_predicates()
            continue
            if n_sharp_predicates > len(sharp_predicates):
                print(f'Unrefined {n_sharp_predicates - len(sharp_predicates)} predicates')
                # TODO: we may have to run Houdini again, as we may get less ctis but no invariants. we can actually get new states.
                # n_states = len(states)
                # n_inductive_invariant = len(inductive_invariant)
                # n_reachable = len(reachable)
                # current_ctis = frozenset()
                # houdini_frames()
                # assert n_states == len(states)
                # assert n_inductive_invariant == len(inductive_invariant)
                # assert n_reachable == len(reachable)

        assert_invariants()

        # print status and possibly terminate
        print(f'\n[{datetime.now()}] Current live states ({len(live_states)} total, {len(reachable)} reachable, {len(ctis)} ctis, {len(current_ctis)} current ctis):\n' + '-' * 8)
        for i in sorted(live_states):
            notes: List[str] = []
            if i in reachable:
                notes.append('reachable')
            if i in current_ctis:
                notes.append('current cti')
            elif i in ctis:
                notes.append('cti')
            note = '(' + ', '.join(notes) + ')'
            print(f'states[{i:3}]{note}:\n{states[i]}\n' + '-' * 80)
        for i in reachable:
            if not cheap_check_implication([states[i].as_onestate_formula(0)], safety):
                print(f'\nFound safety violation by reachable state (states[{i}]).')
                dump_caches()
                return 'UNSAFE'
        print(f'\n[{datetime.now()}] Current sharp predicates ({len(sharp_predicates)} total, {len(inductive_invariant)} proven):')
        for i in sorted(sharp_predicates):
            max_frame = max(j for j, f in enumerate(frames) if predicates[i] in f)
            assert max_frame < len(frames) - 1 or i in inductive_invariant
            note = (' (invariant)' if i in inductive_invariant else f' ({max_frame + 1})')
            max_frame = max(j for j, f in enumerate(step_frames) if predicates[i] in f)
            assert max_frame < len(step_frames) - 1 or i in inductive_invariant
            if i not in inductive_invariant:
                note += f' ({max_frame + 1})'
            print(f'  predicates[{i:3}]{note}: {predicates[i]}')
        if len(inductive_invariant) > 0 and cheap_check_implication([predicates[i] for i in sorted(inductive_invariant)], safety):
            print('Proved safety!')
            dump_caches()
            return 'SAFE'
        print(f'\n[{datetime.now()}] Current bounds:')
        for i in sorted(live_states - reachable):
            if i in state_bounds or i in current_ctis:
                note = ' (current cti)' if i in current_ctis else ''
                n = sum(len(u) for u in states[i].univs.values())
                print(f'  states[{i:3}]{note}: universe is {n}, bound is {state_bounds[i]}')
        print()

        # try to increase bounds for some states, without discovering
        # new CTIs, and add new predicates

        n_predicates = len(predicates)
        n_sharp_predicates = len(sharp_predicates)
        # Different alternatives for which states to bound:
        #
        states_to_bound = sorted(ctis - reachable)  # TODO: live_states - reachable? this was too much work TODO: maybe just pick state with minimal bound
        #
        # states_to_bound = sorted(current_ctis)
        # states_to_bound = [
        #     # bound only a single state, with minimal current bound, then minimal universe size, then minimal index (oldest)
        #     min(current_ctis, key=lambda i: (
        #         state_bounds[i],
        #         sum(len(u) for u in states[i].univs.values()),
        #         i)
        #     )
        # ]
        print(f'Selected the following states for refinement: {states_to_bound}\n')
        added_so_far: List[Predicate] = []
        for i in states_to_bound:
            if i not in bmced:
                print(f'Trying to reach states[{i}] in up to 2 steps')
                p = maps[i].to_clause(maps[i].all_n)
                changes = False
                for k in range(1, 3):
                    print(f'Checking if init satisfies WP_{k} of ~states[{i}]... ',end='')
                    res = check_k_state_implication(solver, inits, p, k)
                    if res is not None:
                        prestate, *poststates = res
                        # add all states, including first one that is an initial state
                        # add new initial state
                        i_pre = add_state(prestate)
                        reachable |= {i_pre}
                        for poststate in poststates:
                            i_post = add_state(poststate)
                            transitions.append((i_pre, i_post))
                            # reachable |= {i_post} # not doing this to trigger discovery of new reachable states on the next loop iteration
                            i_pre = i_post
                        changes = True
                        break
                    else:
                        print('YES')
                if changes:
                    print(f'Managed to reach states[{i}], looping\n')
                    break # TODO: think about this
                else:
                    bmced |= {i}

            if not all(eval_in_state(None, states[i], p) for p in added_so_far):
                print(f'\nstates[{i}] already ruled out by previously added predicates, skipping it')
                continue
                # TODO: this is not entirely consistent with the
                # bounds, since it may be eliminated by predicates
                # with a higher bound
            assert_invariants()
            n = 0
            worklist: List[Tuple[int, ...]] = [(i, )]
            while len(worklist) > 0:  # TODO: rethink the condition of this loop and its structure
                print(f'\nWorking on the bound of states[{i}], current bound is {n}, worklist is {len(worklist)} long:')
                for w in worklist:
                    print(f'  {w}')
                next_worklist: List[Tuple[int, ...]] = []
                for states_to_exclude in worklist:
                    while True:
                        _inv, _ctis = get_invariant(states_to_exclude)
                        if _inv is None:
                            break
                        else:
                            # check if inv is initial
                            initial = True
                            for p in _inv:
                                s = check_initial(solver, p)
                                if s is not None:
                                    print(f'Suggested predicate ({p}) not initial, learned a new initial state')
                                    # assert s not in states # TODO: this can be violated by a backward transition finding an initial state, and should be fixed by a better forward_explore
                                    reachable |= {add_state(s)}
                                    new_reachable_states()
                                    initial = False
                            if initial:
                                break
                    if _inv is not None:
                        # found potential invariant that does not currently has a CTI
                        for p in _inv:
                            add_predicate(p, i)
                            added_so_far.append(p)
                            # TODO: cleanup irrelevant states, i.e.,
                            # states that do not contribute to the
                            # bound of any other state.
                        worklist = []
                        break
                    else:
                        assert _ctis is not None
                        if len(set(states_to_exclude) & reachable) > 0:
                            print(f'Learned that states{sorted(set(states_to_exclude) & reachable)} are reachable, so they cannot be excluded')
                        else:
                            assert len(_ctis) > 0
                            print(f'Could not find invariant, ctis: {sorted(_ctis)}')
                            next_worklist.extend(states_to_exclude + (j,) for j in _ctis)
                else:
                    n += 1
                    worklist = sorted(set(next_worklist))
                    if len(worklist) == 0:
                        assert i in reachable
            if i in reachable:
                print(f'Learned that states[{i}] is reachable, so it cannot be excluded')
                if i in state_bounds:
                    del state_bounds[i]
            else:
                assert _inv is not None
                state_bounds[i] = n
                print(f'The bound for states[{i}] is {n}, the candidate invariant is:')
                for p in _inv:
                    print(f'  {p}')
        # assert len(sharp_predicates) > n_sharp_predicates # this may not be true if the state(s) we selected to refine turns out to be reachable, TODO: rethink this
        print(f'\nLearned {len(predicates) - n_predicates} new predicates and revived {len(sharp_predicates) - n_sharp_predicates - len(predicates) + n_predicates} previous predicates, looping\n')


def cdcl_predicate_bounds(solver: Solver) -> str:
    '''
    Another attempt at CDCL with bounds (not sharp), this time all bounds are for predicates
    '''
    prog = syntax.the_program
    global cache_path
    cache_path = Path(utils.args.filename).with_suffix('.cache')
    load_caches()

    print(f'\nStarting cdcl_predicate_bounds, PID={os.getpid()} [{datetime.now()}]\n')

    # safety = tuple(inv.expr for inv in prog.invs() if inv.is_safety)
    safety = tuple(chain(*(as_clauses(inv.expr) for inv in prog.invs() if inv.is_safety))) # must be in CNF for use in eval_in_state
    # inits = tuple(init.expr for init in prog.inits())
    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # must be in CNF for use in eval_in_state
    assert cheap_check_implication(inits, safety), 'Initial states not safe'

    states: List[State] = []
    maps: List[SubclausesMapTurbo] = []  # for each state, a map with the negation of its diagram
    # the following are indices into states:
    reachable: FrozenSet[int] = frozenset()
    live_states: FrozenSet[int] = frozenset() # not yet ruled out by invariant
    transitions: List[Tuple[int, int]] = [] # TODO: maybe should be frozenset
    substructure: List[Tuple[int, int]] = [] # TODO: maybe should be frozenset

    def add_state(s: State) -> int:
        nonlocal live_states
        assert all(eval_in_state(None, s, predicates[j]) for j in sorted(inductive_invariant))
        if s in states:
            # assert False
            i = states.index(s)
            assert i in live_states
            return i
        i = len(states)
        states.append(s)
        live_states |= {i}
        for j in range(i):
            t = states[j]
            if is_substructure(s, t):
                substructure.append((j, i))
            if is_substructure(t, s):
                substructure.append((i, j))
        cs = as_clauses(Not(s.as_diagram(0).to_ast()))
        assert len(cs) == 1
        c = cs[0]
        maps.append(SubclausesMapTurbo(c, states, [], True))
        return i

    predicates: List[Predicate] = []
    inductive_invariant: FrozenSet[int] = frozenset()  # indices into predicates for current inductive invariant
    sharp_predicates: FrozenSet[int] = frozenset()  # TODO: change name, not necessarily sharp
    frames: List[List[Predicate]] = []
    reason_for_predicate: Dict[int, FrozenSet[int]] = defaultdict(frozenset) # for each predicate index, the indices of the states it helps to exclude
    predicate_bounds: Dict[int, int] = defaultdict(int)  # mapping from predicate index to its invariant

    def add_predicate(p: Predicate, reason: Optional[int] = None) -> int:
        nonlocal predicates
        nonlocal sharp_predicates
        nonlocal reason_for_predicate
        if p not in predicates:
            print(f'add_predicate: adding new predicate: {p}')
            j = len(predicates)
            predicates.append(p)
        else:
            j = predicates.index(p)
            if j in sharp_predicates:
                print(f'add_predicate: already have this predicate: {p}')
            else:
                print(f'add_predicate: reviving previous predicate: {p}')
        sharp_predicates |= {j}
        assert all(eval_in_state(None, states[i], p) for i in sorted(reachable))
        if reason is not None:
            reason_for_predicate[j] |= {reason}
        return j

    for p in safety:
        add_predicate(p)

    def alpha_sharp(states: Collection[State]) -> Sequence[Expr]:
        return alpha_from_predicates(
            solver,
            states,
            [predicates[i] for i in sorted(sharp_predicates)],
        )

    def close_forward(s: FrozenSet[int]) -> FrozenSet[int]:
        '''
        return closure under *abstract* post, also adds all known reachable states.
        abstract post meanst we consider an abstract transition from s to t if t is a substructure of s.
        '''
        r = s | frozenset(reachable)
        changes = True
        while changes:
            changes = False
            # close under transitions and substructure
            for i, j in chain(transitions, substructure):
                if i in r and j not in r:
                    r |= {j}
                    changes = True
        return r

    def forward_explore_from_states(src: FrozenSet[int],
                                   # k: int
    ) -> None:
        # forward explore (concretley) either from the given states,
        # according to the current sharp predicates, using unrolling
        # of k

        # NOTE: this may find new reachable states
        print(f'Starting forward_explore_from_states({sorted(src)})')

        nonlocal reachable
        r: FrozenSet[int] = reachable | src
        r = close_forward(r)
        a = list(chain(
            ## (maps[k].to_clause(maps[k].all_n) for k in sorted(live_states - r)), # to try to connect to existing states or their superstructures
            (predicates[j] for j in sorted(sharp_predicates)),
        ))
        def alpha_a(states: Collection[State]) -> Sequence[Expr]:
            return alpha_from_predicates(solver, states, a)
        n = -1
        while len(r) > n:
            n = len(r)
            r = close_forward(r)
            _states, _a, _initials, _transitions = forward_explore(
                # TODO: this does not connect already discovered states
                # TODO: use unrolling
                solver,
                alpha_a,
                [states[i] for i in sorted(r)],
            )
            a = list(_a)
            assert _states[:len(r)] == [states[i] for i in sorted(r)]
            index_map: Dict[int, int] = dict()
            for i in range(len(_states)):
                try:
                    index_map[i] = states.index(_states[i])
                except ValueError:
                    index_map[i] = add_state(_states[i])
            assert [index_map[i] for i in range(len(r))] == sorted(r)
            n_reachable = len(reachable)
            reachable |= set(index_map[i] for i in _initials)
            for i, j in _transitions:
                ii, jj = index_map[i], index_map[j]
                transitions.append((ii, jj))
            reachable = close_forward(reachable)
            r = close_forward(r)
            assert frozenset(index_map.values()) <= r
        print(f'Finished forward_explore_from_states({sorted(src)})')

    def houdini_frames() -> None:
        '''Check if any subset of the sharp predicates is inductive, and
        possibly add new ctis. This version is stratified, and
        computes "frames" similar to IC3, but since multi-transition
        CTIs are used they have a slightly different meaning. This

        This version calls forward_explore_from_states on its own, and
        may find new reachable states, both when doing
        forward_explore_from_states of the reachable states, but also
        since we may find a CTI and then discover that the prestate is
        reachable all at once. Maybe this should be changed to be more
        consistent by treating negations of diagrams as predicates and
        not as a special case

        '''
        nonlocal reachable
        nonlocal inductive_invariant
        nonlocal frames
        assert_invariants()

        # first forward_explore from the reachable states
        n_reachable = len(reachable)
        n_sharp_predicates = len(sharp_predicates)
        forward_explore_from_states(reachable)
        new_reachable_states()
        print(f'Forward explore of reachable states found {len(reachable) - n_reachable} new reachable states, eliminating {len(sharp_predicates) - n_sharp_predicates} predicates')
        assert_invariants()

        frames = [[predicates[i] for i in sorted(sharp_predicates)]]
        r = reachable
        while True:
            assert r == close_forward(r)
            a = frames[-1]
            assert all(eval_in_state(None, states[i], p) for i, p in product(sorted(r), a))
            for i in sorted(live_states):
                if i not in r and all(eval_in_state(None, states[i], p) for p in a):
                    r |= {i}
                    r = close_forward(r)
            n_reachable = len(reachable)
            forward_explore_from_states(r) # TODO: not sure if we should do this here or not
            assert n_reachable == len(reachable)
            r = close_forward(r)
            for i in sorted(live_states):
                if i in r:
                    continue
                print(f'houdini_frames: checking for backward-transition from states[{i}]')
                res = check_two_state_implication(
                    solver,
                    a + [maps[i].to_clause(maps[i].all_n)],
                    maps[i].to_clause(maps[i].all_n),
                    f'backward-transition from states[{i}]'
                )
                print(f'houdini_frames: done checking for backward-transition from states[{i}]')
                if res is not None:
                    prestate, poststate = res
                    i_pre = add_state(prestate)
                    i_post = add_state(poststate)
                    transitions.append((i_pre, i_post))
                    assert i_post == i or (i_post, i) in substructure
                    reachable = close_forward(reachable) # we could have learned that i_pre is reachable here.... TODO: this is inconsistent with frames, and this should be fixed
                    r |= {i_pre}
                    r = close_forward(r)
            n_reachable = len(reachable)
            forward_explore_from_states(r) # this is probably a good place for this
            assert n_reachable == len(reachable)
            r = close_forward(r)
            b = [p for p in a if all(eval_in_state(None, states[i], p) for i in sorted(r))]
            for p in b[:]:
                if p not in b:
                    continue
                print(f'houdini_frames: checking for CTI to {p}')
                res = check_two_state_implication(solver, a, p, 'CTI')
                print(f'houdini_frames: done checking for CTI to {p}')
                if res is not None:
                    prestate, poststate = res
                    i_pre = add_state(prestate)
                    i_post = add_state(poststate)
                    transitions.append((i_pre, i_post))
                    reachable = close_forward(reachable) # we could have learned that i_pre is reachable here.... TODO: this is inconsistent with frames, and this should be fixed
                    r |= {i_pre}
                    r = close_forward(r)
                    n_reachable = len(reachable)
                    forward_explore_from_states(r) # this is probably a good place for this
                    assert n_reachable == len(reachable)
                    r = close_forward(r)
                    b = [p for p in b if all(eval_in_state(None, states[i], p) for i in sorted(r))]
            if a == b:
                break
            else:
                frames.append(b)
        # here, frames[-1] is inductive (but it may not imply safety)
        assert frames[-1] == a == b
        inv = frozenset(predicates.index(p) for p in a)
        assert inductive_invariant <= inv
        inductive_invariant = inv

    def get_invariant(top_clauses: Sequence[Expr], states_to_exclude: FrozenSet[int]) -> Tuple[Optional[List[Predicate]], Optional[List[int]]]:
        '''Check if there is an inductive invariant that is a conjunction of
        one subclause from each top clause, that excludes all given
        states. Either return an invariant (list of Predicates) or a
        list of CTIs (which may be some of the states_to_exclude).

        '''
        mp = MultiSubclausesMapICE(
            top_clauses,
            states,
            [],
            False
        )
        def check_sep(s: FrozenSet[int]) -> Optional[List[Predicate]]:
            res = mp.separate(
                pos=sorted(reachable),
                imp=[(i, j) for i in sorted(s) for j in sorted(close_forward(frozenset([i])))],
                neg=(states_to_exclude & s),
            )
            if res is None:
                return None
            else:
                return [mp.to_clause(k, res[k]) for k in range(mp.m)]
        ctis = live_states - reachable
        res = check_sep(ctis)
        if res is not None:
            return res, None
        # minimize ctis
        # TODO: use unsat cores
        for i in sorted(ctis):
            if i in ctis and check_sep(ctis - {i}) is None:
                ctis -= {i}
        assert check_sep(ctis) is None
        return None, sorted(ctis)

    def new_reachable_states() -> None:
        nonlocal sharp_predicates
        nonlocal reachable
        reachable = close_forward(reachable)
        sharp_predicates = frozenset(
            j for j in sorted(sharp_predicates)
            if all(eval_in_state(None, states[k], predicates[j])
                   for k in sorted(reachable)
            )
        )

    def assert_invariants() -> None:
        # for debugging
        assert reachable == close_forward(reachable)
        assert sharp_predicates <= frozenset(
            j for j, p in enumerate(predicates)
            if all(eval_in_state(None, states[k], p)
                   for k in sorted(reachable)
            )
        )
        assert live_states == frozenset(
            i for i, s in enumerate(states)
            if all(eval_in_state(None, s, predicates[j])
                   for j in sorted(inductive_invariant)
            )
        )
        for i in sorted(sharp_predicates - inductive_invariant):
            assert predicates[i] in safety or len(reason_for_predicate[i]) > 0
        for x in reason_for_predicate.values():
            assert x <= live_states

    while True:
        assert_invariants() # not true if we have BMC, TODO rethink this

        # Houdini, to check if anything new is inductive, adding new
        # reachable states and new ctis, which will be used later when
        # computing bounds
        n_inductive_invariant = len(inductive_invariant)
        n_reachable = len(reachable)
        houdini_frames()
        if len(reachable) > n_reachable:
            print(f'Houdini found {len(reachable) - n_reachable} new reachable states')
            new_reachable_states()
        if len(inductive_invariant) > n_inductive_invariant:
            print(f'Houdini found {len(inductive_invariant) - n_inductive_invariant} new inductive predicates')
            live_states = frozenset(
                i for i, s in enumerate(states)
                if all(eval_in_state(None, s, predicates[j])
                       for j in sorted(inductive_invariant)
                )
            )
            predicate_bounds.clear()  # TODO: maybe do something a bit better, i.e., record the set of states explaining the bound, and keep it if they are still live
            for i in reason_for_predicate:
                reason_for_predicate[i] &= live_states
            n_sharp_predicates = len(sharp_predicates)
            sharp_predicates = inductive_invariant | frozenset(
                j for j in sharp_predicates
                if len(reason_for_predicate[j]) > 0 or predicates[j] in safety
            )
            if n_sharp_predicates > len(sharp_predicates):
                print(f'Unrefined {n_sharp_predicates - len(sharp_predicates)} predicates')
                # TODO: we may have to run Houdini again, as we may get less ctis but no invariants. we can actually get new states.
                # n_states = len(states)
                # n_inductive_invariant = len(inductive_invariant)
                # n_reachable = len(reachable)
                # current_ctis = frozenset()
                # houdini_frames()
                # assert n_states == len(states)
                # assert n_inductive_invariant == len(inductive_invariant)
                # assert n_reachable == len(reachable)

        assert_invariants()

        # print status and possibly terminate
        print(f'\n[{datetime.now()}] Current live states ({len(live_states)} total, {len(reachable)} reachable):\n' + '-' * 8)
        for i in sorted(live_states):
            notes: List[str] = []
            if i in reachable:
                notes.append('reachable')
            note = '(' + ', '.join(notes) + ')'
            print(f'states[{i:3}]{note}:\n{states[i]}\n' + '-' * 80)
        for i in reachable:
            if not cheap_check_implication([states[i].as_onestate_formula(0)], safety):
                print(f'\nFound safety violation by reachable state (states[{i}]).')
                dump_caches()
                return 'UNSAFE'
        print(f'\n[{datetime.now()}] Current sharp predicates ({len(sharp_predicates)} total, {len(inductive_invariant)} proven):')
        for i in sorted(sharp_predicates):
            max_frame = max(j for j, f in enumerate(frames) if predicates[i] in f)
            assert max_frame < len(frames) - 1 or i in inductive_invariant
            note = (' (invariant)' if i in inductive_invariant else f' ({max_frame + 1})')
            print(f'  predicates[{i:3}]{note}: {predicates[i]}')
        if len(inductive_invariant) > 0 and cheap_check_implication([predicates[i] for i in sorted(inductive_invariant)], safety):
            print('Proved safety!')
            dump_caches()
            return 'SAFE'
        print(f'\n[{datetime.now()}] Current bounds:')
        for i in sorted(sharp_predicates - inductive_invariant):
            if i in predicate_bounds:
                # TODO: actually the bound for every predicate here is at least 1
                print(f'  predicates[{i:3}]: bound is {predicate_bounds[i]}, ({predicates[i]})')
        print()

        # try to increase bounds for some predicates, without
        # discovering new CTIs (but may discover new reachable
        # states), and add new predicates

        n_predicates = len(predicates)
        n_sharp_predicates = len(sharp_predicates)
        #predicates_to_bound = sorted(sharp_predicates - inductive_invariant)
        predicates_to_bound = sorted(j for j in sharp_predicates if predicates[j] in safety)
        print(f'Selected the following predicates for refinement: {predicates_to_bound}\n')
        # live_so_far: live_states
        for j in predicates_to_bound:
            # TODO: maybe skip predicates that have already been proven using existing new predicates
            assert_invariants()
            states_to_exclude = frozenset(
                i for i in live_states - reachable
                if not eval_in_state(None, states[i], predicates[j])
            )
            n = 0
            worklist: List[Tuple[int, ...]] = [()]
            while len(worklist) > 0:  # TODO: rethink the condition of this loop and its structure
                print(f'\nWorking on the bound of predicates[{j}], states_to_exclude={sorted(states_to_exclude)}, current bound is {n}, worklist is {len(worklist)} long:')
                for w in worklist:
                    print(f'  {w}')
                next_worklist: List[Tuple[int, ...]] = []
                for ii in worklist:
                    n_reachable = len(reachable)
                    while True:
                        _inv, _ctis = get_invariant(
                            # TODO: should the predicate we are trying
                            # to prove also be used in the invariant?
                            # right now it is not
                            [maps[i].to_clause(maps[i].all_n) for i in ii],
                            states_to_exclude,
                        )
                        if _inv is None:
                            break
                        else:
                            # check if inv is initial
                            initial = True
                            for p in _inv:
                                s = check_initial(solver, p)
                                if s is not None:
                                    print(f'Suggested predicate ({p}) not initial, learned a new initial state')
                                    # assert s not in states # TODO: this can be violated by a backward transition finding an initial state, and should be fixed by a better forward_explore
                                    reachable |= {add_state(s)}
                                    new_reachable_states()
                                    initial = False
                            if initial:
                                break
                    print(f'Learned {len(reachable) - n_reachable} new reachable states')
                    if _inv is not None:
                        # found potential invariant that does not currently has a CTI
                        assert len(_inv) == len(ii)
                        assert all(
                            not all(eval_in_state(None, states[i], p) for p in _inv)
                            for i in sorted(states_to_exclude)
                        )
                        assert all(
                            all(eval_in_state(None, states[i], p) for p in _inv)
                            for i in sorted(reachable)
                        )
                        for p, i in zip(_inv, ii):
                            add_predicate(p, i)
                        worklist = []
                        break
                    else:
                        assert _ctis is not None
                        # note: _ctis may be empty here
                        print(f'Could not find invariant, ctis: {sorted(_ctis)}')
                        next_worklist.extend(ii + (i,) for i in sorted(_ctis))
                else:
                    n += 1
                    worklist = sorted(set(next_worklist))
                    if len(worklist) == 0:
                        assert len(states_to_exclude & reachable) > 0
            if len(states_to_exclude & reachable) > 0:
                print(f'Learned that predicates[{j}] is violated by a reachable state')
                if j in predicate_bounds:
                    del predicate_bounds[j]
            else:
                assert _inv is not None
                predicate_bounds[j] = n
                print(f'The bound for predicates[{j}] is {n}, the candidate invariant is:')
                for p in _inv:
                    print(f'  {p}')

        print(f'\n[{datetime.now()}] Current bounds:')
        for i in sorted(sharp_predicates - inductive_invariant):
            if i in predicate_bounds:
                # TODO: actually the bound for every predicate here is at least 1
                print(f'  predicates[{i:3}]: bound is {predicate_bounds[i]}, ({predicates[i]})')
        print()

        print(f'\nLearned {len(predicates) - n_predicates} new predicates and revived {len(sharp_predicates) - n_sharp_predicates - len(predicates) + n_predicates} previous predicates, looping\n')


def primal_dual_houdini(solver: Solver) -> str:
    '''
    Another attempt primal dual Houdini
    '''
    prog = syntax.the_program
    global cache_path
    cache_path = Path(utils.args.filename).with_suffix('.cache')
    load_caches()

    print(f'\nStarting primal_dual_houdini, PID={os.getpid()} [{datetime.now()}]\n')

    safety = tuple(chain(*(as_clauses(inv.expr) for inv in prog.invs() if inv.is_safety))) # must be in CNF for
    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # must be in CNF for use in eval_in_state
    assert cheap_check_implication(inits, safety), 'Initial states not safe'

    states: List[State] = [] # used both for the high level houdini states (reachable, live_states) and the internal CTIs of the "dual edge solver" (internal_ctis)
    maps: List[SubclausesMapTurbo] = []  # for each state, a map with the negation of its diagram, not really used, but still used to get the negation of diagram of a state TODO: remove
    # the following are indices into states:
    reachable: FrozenSet[int] = frozenset()
    live_states: FrozenSet[int] = frozenset() # not yet ruled out by invariant, and also currently active in the houdini level
    internal_ctis: FrozenSet[int] = frozenset() # internal CTIs used by the "dual edge solver"
    transitions: List[Tuple[int, int]] = [] # TODO: maybe should be frozenset
    substructure: List[Tuple[int, int]] = [] # TODO: maybe should be frozenset
    # bmced: FrozenSet[int] = frozenset() # we have already used BMC to check that this state is not reachable from init in 2 steps (will be made more general later)

    predicates: List[Predicate] = []
    inductive_invariant: FrozenSet[int] = frozenset()  # indices into predicates for current inductive invariant
    live_predicates: FrozenSet[int] = frozenset()  # currently active predicates, not violated by reachable states
    dual_transitions: List[Tuple[FrozenSet[int], FrozenSet[int]]] = [] # indices into predicates, TODO: maybe should be frozenset
    #TODO: maybe have "dual_substructure", i.e., implications

    frames: List[List[Predicate]] = []
    step_frames: List[List[Predicate]] = []

    dual_frames: List[List[int]] = [] # ints are indicites into states
    # TODO: daul_step_frames?

    # reason_for_predicate: Dict[int, FrozenSet[int]] = defaultdict(frozenset) # for each predicate index, the indices of the states it helps to exclude # TODO: maybe bring this back here, but some predicates are to rule out actual states, and some just for internal CTIs

    def add_state(s: State, internal_cti: bool) -> int:
        nonlocal live_states
        nonlocal internal_ctis
        assert all(eval_in_state(None, s, predicates[j]) for j in sorted(inductive_invariant))
        note = ' (internal cti)' if internal_cti else ' (live state)'
        if s not in states:
            print(f'add_state{note}: checking for substructures... ', end='')
            work = list(chain(
                ((s, t) for t in states),
                ((t, s) for t in states),
            ))
            if utils.args.cpus is None or utils.args.cpus == 1 or len(work) <= 1:
                results = [is_substructure(u, v) for u, v in work]
            else:
                with multiprocessing.Pool(min(utils.args.cpus, len(work))) as pool:
                    results = pool.starmap_async(
                        is_substructure,
                        work,
                    ).get(9999999)
            is_substructure_results = dict(zip(work, results))
            substructures = frozenset(
                i for i, t in enumerate(states)
                if is_substructure_results[(t, s)]
            )
            superstructures = frozenset(
                i for i, t in enumerate(states)
                if is_substructure_results[(s, t)]
            )
            if False:
                assert substructures == frozenset(
                    i for i, t in enumerate(states)
                    if is_substructure(t, s)
                )
                assert superstructures == frozenset(
                    i for i, t in enumerate(states)
                    if is_substructure(s, t)
                )
            print(f'done')
            isomorphic = substructures & superstructures
            if len(isomorphic) > 0:
                assert len(isomorphic) == 1, sorted(isomorphic)
                i = list(isomorphic)[0]
                print(f'add_state{note}: isomorphic to previous state: states[{i}]')
            else:
                i = len(states)
                print(f'add_state{note}: adding new state: states[{i}]')
                states.append(s)
                for j in sorted(substructures):
                    substructure.append((i, j))
                for j in sorted(superstructures):
                    substructure.append((j, i))
                cs = as_clauses(Not(s.as_diagram(0).to_ast()))
                assert len(cs) == 1
                c = cs[0]
                maps.append(SubclausesMapTurbo(c, states, [], True))
            if internal_cti:
                internal_ctis |= {i}
            else:
                live_states |= {i}
            return i
        else:
            i = states.index(s)
            if internal_cti:
                if i not in internal_ctis:
                    print(f'add_state{note}: adding states[{i}] to internal_ctis')
                    internal_ctis |= {i}
                else:
                    print(f'add_state{note}: already have states[{i}] in internal_ctis')
            else:
                if i not in live_states:
                    print(f'add_state{note}: adding states[{i}] to live_states')
                    live_states |= {i}
                else:
                    print(f'add_state{note}: already have states[{i}] in live_states')
            return i

    def add_transition(i: int, j: int) -> None:
        nonlocal transitions
        nonlocal live_states
        nonlocal reachable
        assert 0 <= i < len(states)
        assert 0 <= j < len(states)
        if (i, j) not in transitions:
            transitions.append((i, j))
            # TODO: think about this, right now this may cause new states to be reachable and live
            reachable = close_forward(reachable, True)
            live_states |= reachable
        else:
            #assert False, (i, j) # TODO: think about this more. this usually happens when j was previously only an internal cti
            pass

    def add_predicate(p: Predicate, reason: Optional[int] = None) -> int:
        nonlocal predicates
        nonlocal live_predicates
        # nonlocal reason_for_predicate
        if p not in predicates:
            j = len(predicates)
            print(f'add_predicate: adding new predicate {j}: {p}')
            predicates.append(p)
        else:
            j = predicates.index(p)
            if j in live_predicates:
                print(f'add_predicate: already have this predicate {j}: {p}')
            else:
                print(f'add_predicate: reviving previous predicate {j}: {p}')
        live_predicates |= {j}
        #TODO# assert all(eval_in_state(None, states[i], p) for i in sorted(reachable))
        if reason is not None:
            assert False # maybe this will change later
            # reason_for_predicate[j] |= {reason}
        return j

    for p in safety:
        add_predicate(p)

    def close_forward(s: FrozenSet[int], include_internal_ctis: bool = False) -> FrozenSet[int]:
        '''
        return closure under *abstract* post, also adds all known reachable states.
        abstract post meanst we consider an abstract transition from s to t if t is a substructure of s.
        '''
        r = s | frozenset(reachable)
        changes = True
        while changes:
            changes = False
            # close under transitions and substructure
            for i, j in chain(transitions, substructure):
                if i in r and j not in r and (j in live_states or (include_internal_ctis and j in internal_ctis)):
                    # TODO: if j is an internal_cti, maybe we want to make it live?
                    r |= {j}
                    changes = True
        return r

    def dual_close_forward(s: FrozenSet[int]) -> FrozenSet[int]:
        '''
        return closure under *abstract* post, also adds all known reachable states.
        abstract post meanst we consider an abstract transition from s to t if t is a substructure of s.
        '''
        r = s | frozenset(inductive_invariant)
        changes = True
        while changes:
            changes = False
            # close under transitions and substructure
            for ii, jj in dual_transitions: # TODO: maybe chain(dual_transitions, implications)
                if ii <= r and not jj <= r:
                    r |= jj
                    changes = True
        return r

    def forward_explore_from_states(src: FrozenSet[int],
                                   # k: int
    ) -> None:
        # forward explore (concretley) either from the given states,
        # according to the current sharp predicates, using unrolling
        # of k
        # NOTE: this may find new reachable states
        print(f'Starting forward_explore_from_states({sorted(src)})')
        nonlocal reachable
        r: FrozenSet[int] = reachable | src
        r = close_forward(r)
        a = [predicates[j] for j in sorted(live_predicates)]
        def alpha_a(states: Collection[State]) -> Sequence[Expr]:
            return alpha_from_predicates(solver, states, a)
        n = -1
        while len(r) > n:
            n = len(r)
            r = close_forward(r)
            _states, _a, _initials, _transitions = forward_explore(
                # TODO: this does not connect already discovered states
                # TODO: use unrolling
                solver,
                alpha_a,
                [states[i] for i in sorted(r)],
            )
            a = list(_a)
            assert _states[:len(r)] == [states[i] for i in sorted(r)]
            index_map = {
                i: add_state(s, False)
                if s not in states or states.index(s) not in live_states else
                states.index(s)
                for i, s in enumerate(_states)
            }
            assert [index_map[i] for i in range(len(r))] == sorted(r)
            n_reachable = len(reachable)
            reachable |= set(index_map[i] for i in _initials)
            for i, j in _transitions:
                i, j = index_map[i], index_map[j]
                if (i, j) not in transitions:
                    add_transition(i, j)
                else:
                    #assert False, (i, j) # TODO: this can happen if j was not a live state before
                    pass
            reachable = close_forward(reachable)
            r = close_forward(r)
            assert frozenset(index_map.values()) <= r
        print(f'Finished forward_explore_from_states({sorted(src)})')

    def houdini_frames() -> None:
        '''Check if any subset of the sharp predicates is inductive, and
        possibly add new ctis. This version is stratified, and
        computes "frames" similar to IC3, but since multi-transition
        CTIs are used they have a slightly different meaning. This

        This version calls forward_explore_from_states on its own, and
        may find new reachable states, both when doing
        forward_explore_from_states of the reachable states, but also
        since we may find a CTI and then discover that the prestate is
        reachable all at once. Maybe this should be changed to be more
        consistent by treating negations of diagrams as predicates and
        not as a special case

        '''
        nonlocal reachable
        nonlocal inductive_invariant
        nonlocal frames
        assert_invariants()

        # first forward_explore from the reachable states
        n_reachable = len(reachable)
        n_live_predicates = len(live_predicates)
        forward_explore_from_states(reachable)
        new_reachable_states()
        print(f'Forward explore of reachable states found {len(reachable) - n_reachable} new reachable states, eliminating {n_live_predicates - len(live_predicates)} predicates')
        assert_invariants()

        frames = [[predicates[i] for i in sorted(live_predicates)]]
        r = reachable
        while True:
            assert r == close_forward(r)
            a = frames[-1]
            assert all(eval_in_state(None, states[i], p) for i, p in product(sorted(r), a))
            for i in sorted(live_states):
                if i not in r and all(eval_in_state(None, states[i], p) for p in a):
                    r |= {i}
                    r = close_forward(r)
            n_reachable = len(reachable)
            forward_explore_from_states(r) # TODO: not sure if we should do this here or not
            assert n_reachable == len(reachable)
            r = close_forward(r)
            for i in sorted(live_states):
                if i in r:
                    continue
                print(f'houdini_frames: checking for backward-transition from states[{i}]')
                res = check_two_state_implication(
                    solver,
                    a + [maps[i].to_clause(maps[i].all_n)],
                    maps[i].to_clause(maps[i].all_n),
                    f'backward-transition from states[{i}]'
                )
                print(f'houdini_frames: done checking for backward-transition from states[{i}]')
                if res is not None:
                    prestate, poststate = res
                    i_pre = add_state(prestate, False)
                    i_post = add_state(poststate, False)
                    add_transition(i_pre, i_post)
                    assert i_post == i or (i_post, i) in substructure
                    reachable = close_forward(reachable) # we could have learned that i_pre is reachable here.... TODO: this is inconsistent with frames, and this should be fixed
                    r |= {i_pre}
                    r = close_forward(r)
            n_reachable = len(reachable)
            forward_explore_from_states(r) # this is probably a good place for this
            assert n_reachable == len(reachable)
            r = close_forward(r)
            b = [p for p in a if all(eval_in_state(None, states[i], p) for i in sorted(r))]
            for p in b[:]:
                if p not in b or predicates.index(p) in inductive_invariant:
                    continue
                print(f'houdini_frames: checking for CTI to {p}')
                res = check_two_state_implication(solver, a, p, 'CTI')
                print(f'houdini_frames: done checking for CTI to {p}')
                if res is not None:
                    prestate, poststate = res
                    i_pre = add_state(prestate, False)
                    i_post = add_state(poststate, False)
                    if (i_pre, i_post) not in transitions:
                        add_transition(i_pre, i_post)
                        reachable = close_forward(reachable) # we could have learned that i_pre is reachable here.... TODO: this is inconsistent with frames, and this should be fixed
                    else:
                        assert i_pre not in r
                    r |= {i_pre}
                    r = close_forward(r)
                    n_reachable = len(reachable)
                    forward_explore_from_states(r) # this is probably a good place for this
                    assert n_reachable == len(reachable)
                    r = close_forward(r)
                    b = [p for p in b if all(eval_in_state(None, states[i], p) for i in sorted(r))]
            if a == b:
                break
            else:
                frames.append(b)
        # here, frames[-1] is inductive (but it may not imply safety)
        assert frames[-1] == a == b
        inv = frozenset(predicates.index(p) for p in a)
        assert inductive_invariant <= inv
        inductive_invariant = inv

    def compute_step_frames() -> None:
        nonlocal step_frames
        print(f'compute_step_frames: starting')
        step_frames = [[predicates[i] for i in sorted(live_predicates)]]
        while True:
            a = step_frames[-1]
            b = []
            for p in a:
                res = check_two_state_implication(solver, a, p, 'step-CTI')
                if res is not None:
                    prestate, poststate = res
                    # TODO: should we add these states or not? they may not necessarily already be in states
                else:
                    b.append(p)
            if a == b:
                break
            else:
                step_frames.append(b)
        # here, frames[-1] is inductive (but it may not imply safety)
        assert step_frames[-1] == a == b
        inv = frozenset(predicates.index(p) for p in a)
        assert inductive_invariant == inv
        print(f'compute_step_frames: done')

    def dual_houdini_frames() -> None:
        '''
        TODO: doc
        note: may find new reachable states, live states, inductive invariants
        '''
        nonlocal reachable
        nonlocal inductive_invariant
        nonlocal dual_frames
        nonlocal live_states
        assert_invariants()
        print(f'dual_houdini_frames: starting')
        # first forward_explore from the current inductive invariant
        n_inductive_invariant = len(inductive_invariant)
        n_reachable_states = len(reachable)
        forward_explore_from_predicates(inductive_invariant)
        new_inductive_invariants()
        new_reachable_states()
        print(f'dual_houdini_frames: forward explore of inductive invariant found {len(inductive_invariant) - n_inductive_invariant} new inductive predicates and {len(reachable) - n_reachable_states} new reachable states')
        assert_invariants()
        # TODO: should we stop here in case we found anything and go back to primal houdini?

        dual_frames = [sorted(live_states)]
        # TODO: there is a consistency problem if new reachable states are discovered during the loop, since they will not be part of previous frames, this should be figured out, maybe by restarting everything if we find a new reachable state
        r = inductive_invariant
        while True:
            assert r == dual_close_forward(r)
            a = dual_frames[-1]
            assert all(eval_in_state(None, states[i], predicates[j]) for i, j in product(a, sorted(r)))
            print(f'dual_houdini_frames: starting iteration, r={sorted(r)}, a=reachable+{sorted(frozenset(a) - reachable)}')
            r_0 = r
            for j in sorted(live_predicates):
                if j not in r and all(eval_in_state(None, states[i], predicates[j]) for i in a):
                    print(f'dual_houdini_frames: adding {j} to r by abstract implication')
                    r |= {j}
                    r = dual_close_forward(r)
            n_reachable = len(reachable)
            n_inductive_invariant = len(inductive_invariant)
            forward_explore_from_predicates(r) # TODO: not sure if we should do this here or not
            assert n_reachable == len(reachable), '?'
            assert n_inductive_invariant == len(inductive_invariant), '?'
            r = dual_close_forward(r)
            # TODO: uncomment this when find_dual_edge supports predicates
            # # try to add edges to existing predicates (dual-backward-transitions)
            # for j in sorted(live_predicates):
            #     if j in r:
            #         continue
            #     print(f'dual_houdini_frames: checking for dual-backward-transition from predicates[{j}]: {predicates[j]}')
            #     res = find_dual_edge(a, r_0, predicates[j], [predicates[j] for j in sorted(live_predicates - r)])
            #     print(f'dual_houdini_frames: done checking for dual-backward-transition from predicates[{j}]: {predicates[j]}')
            #     if res is not None:
            #         ps = frozenset(add_predicate(p) for p in res[0])
            #         qs = frozenset(add_predicate(q) for q in res[1])
            #         dual_transitions.append((ps, qs))
            #         assert j in qs # TODO: or maybe predicates[j] can be implied by the qs ?
            #         n_inductive_invariant = len(inductive_invariant)
            #         inductive_invariant = dual_close_forward(inductive_invariant)
            #         assert n_inductive_invariant == len(inductive_invariant) # TODO: maybe we actually learned a new inductive invariant. this will be inconsisted with the frames, as in primal houdini_frames
            #         r |= ps
            #         r = dual_close_forward(r)
            #         assert qs <= r
            # n_inductive_invariant = len(inductive_invariant)
            # forward_explore_from_predicates(r) # this is probably a good place for this
            # assert n_reachable == len(reachable), '?'
            # assert n_inductive_invariant == len(inductive_invariant), '?'
            # r = dual_close_forward(r)
            # try to exclude more states
            pos = reachable
            changes = True
            while changes:
                changes = False
                pos |= close_forward(reachable)
                roots = compute_roots(
                    s=frozenset(
                        i for i in a
                        if all(eval_in_state(None, states[i], predicates[j]) for j in sorted(r))
                    ),
                    pos=pos,
                    ps=[predicates[j] for j in r_0],
                    a=frozenset(a)
                )
                if len(roots) == 0:
                    continue
                print(f'dual_houdini_frames: trying to eliminate the following {len(roots)} roots: {sorted(roots)}')
                for i in sorted(roots):
                    assert i not in reachable
                    if not all(eval_in_state(None, states[i], predicates[j]) for j in sorted(r)):
                        # already eliminated i
                        assert changes
                        continue
                    print(f'dual_houdini_frames: checking for dual-CTI to states[{i}]')
                    n_reachable = len(reachable)
                    res = find_dual_edge(
                        a,
                        r_0,
                        states[i],
                        [states[i] for i in a
                         if all(eval_in_state(None, states[i], predicates[j]) for j in sorted(r))
                        ],
                    )
                    #TODO# assert n_reachable == len(reachable), '?'
                    print(f'dual_houdini_frames: done checking for dual-CTI to states[{i}]')
                    if res is not None:
                        ps = frozenset(add_predicate(p) for p in res[0])
                        qs = frozenset(add_predicate(q) for q in res[1])
                        dual_transitions.append((ps, qs))
                        n_inductive_invariant = len(inductive_invariant)
                        inductive_invariant = dual_close_forward(inductive_invariant)
                        assert n_inductive_invariant == len(inductive_invariant) # TODO: maybe we actually learned a new inductive invariant. this will be inconsisted with the frames, as in primal houdini_frames
                        r |= ps
                        r = dual_close_forward(r)
                        assert qs <= r
                        n_reachable = len(reachable)
                        n_inductive_invariant = len(inductive_invariant)
                        forward_explore_from_predicates(r)  # this is probably a good place for this
                        #TODO# assert n_reachable == len(reachable), '?'
                        assert n_inductive_invariant == len(inductive_invariant), '?'
                        r = dual_close_forward(r)
                        assert not all(eval_in_state(None, states[i], predicates[j]) for j in sorted(r))
                        changes = True
                        # TODO: should we reset pos here? if not then pos may not be a subset of s in compute_roots
                    else:
                        # learn that we cannot eliminate i directly, so we won't try to eliminate things forward reachable from i
                        pos |= {i}
            if False:
                # just to find bugs in compute_roots
                # TODO: run this sometime on all examples
                for i in sorted(a):
                    if i in reachable or not all(eval_in_state(None, states[i], predicates[j]) for j in sorted(r)):
                        continue
                    assert find_dual_edge(a, r_0, states[i], []) is None, i
            b = [i for i in a if all(eval_in_state(None, states[i], predicates[j]) for j in sorted(r))]
            print(f'dual_houdini_frames: next frame is: {sorted(b)}')
            if a == b:
                break
            else:
                dual_frames.append(b)
        # here, dual_frames[-1] should be the reachable states
        assert dual_frames[-1] == a == b, (dual_frames[-1], a, b)
        # we need to update reachable to include everything reachable via transitions and substructures to internal CTIs, TODO: think more carefully about this
        reachable = close_forward(reachable, True)
        live_states |= reachable
        # TODO: this assertion is actually not true when there is a
        # cycle of unreachable states, we should think about it more
        # assert frozenset(dual_frames[-1]) <= reachable, sorted(frozenset(dual_frames[-1]) - reachable)
        print(f'dual_houdini_frames computed {len(dual_frames)} dual frames:')
        for f in dual_frames:
            print(f'  {sorted(f)}')
        if frozenset(dual_frames[-1]) <= reachable:
            print(f'  last frame contains only reachable states')
        else:
            print(f'  last frame contains some states not known to be reachable')
        print()

    def compute_roots(s: FrozenSet[int], pos: FrozenSet[int], ps: Collection[Predicate], a: Optional[FrozenSet[int]]) -> FrozenSet[int]:
        '''Given a set of states s (as indices), compute a minimal subset of
        it r such that any dual edge (ps', qs') that eliminates a
        state from s must eliminate a state from r, under the
        assumption that ps' are restricted to be the given ps, plust
        predicates that are true for states in a (or no other
        predicates if a is None), and q does not eliminate any state
        from pos.
        '''
        # TODO: think about this again and run more thorough validation tests
        print(f'compute_roots: starting with: s={sorted(s)}, pos=reachable+{sorted(pos - reachable)}, ps={sorted(predicates.index(p) for p in ps)}, a={sorted(a) if a is not None else None}')
        # assert a is None or reachable <= a TODO: this can be violated if a new reachable state is discovered in dual_houdini_frames, think about this
        assert reachable <= pos
        # assert pos <= s TODO: think about this again, but for now I think it makes sense even of pos is not a subset of s
        def v(i: int) -> z3.ExprRef:
            return z3.Bool(f'state_{i}')
        if a is not None:
            dom = a
            for i, j in substructure:
                if i in dom and j not in dom:
                    dom |= {j}
            # no need for fixpoint since substructure is transitive
        else:
            dom = frozenset(range(len(states)))
        dom = frozenset(i for i in dom if all(
            eval_in_state(None, states[i], p) for p in ps
        ))
        z3s = z3.Solver()
        for i in sorted(pos):
            z3s.add(v(i))
        for i, j in sorted(chain(transitions, substructure)):
            if i in dom and j in dom:
                z3s.add(z3.Implies(v(i), v(j)))
        z3s.add(z3.Or(*(z3.Not(v(i)) for i in sorted(s))))
        # print(f'compute_roots: z3s:\n{z3s}')
        def f(r: FrozenSet[int]) -> bool:
            res = z3s.check(*(v(i) for i in r))
            assert res in (z3.unsat, z3.sat)
            return res == z3.unsat
        r = s
        assert f(r)
        for i in sorted(
                r,
                key=lambda i: (-sum(len(u) for u in states[i].univs.values()), -i)
                # try to remove larger (by universe size) and newer states first
        ):
            if f(r - {i}):
                r -= {i}
        assert f(r)
        print(f'compute_roots: s={sorted(s)}, pos=reachable+{sorted(pos - reachable)}, ps={sorted(predicates.index(p) for p in ps)}, a={sorted(a) if a is not None else None}, result is {sorted(r)}')
        return r

    def forward_explore_from_predicates(src: FrozenSet[int],
                                        # k: int
    ) -> None:
        '''
        dual forward explore from the given set of predicates

        adds new predicates, may find new inductive invariant
        adds new internal_ctis, but does not add any new states

        for now, assuming k=1, i.e., to rule out a state we will only use one clause
        '''
        print(f'Starting forward_explore_from_predicates({sorted(src)})')
        nonlocal inductive_invariant
        n_inductive_invariant = len(inductive_invariant)
        r: FrozenSet[int] = inductive_invariant | src
        n_r = len(r)
        r = dual_close_forward(r)
        changes = True
        while changes:
            changes = False
            r = dual_close_forward(r)
            # try to add more known predicates
            for j in sorted(live_predicates):
                if j in r:
                    continue
                cti, ps = check_dual_edge(
                    solver,
                    tuple(predicates[k] for k in sorted(r)),
                    (predicates[j],),
                    # msg='cti?', TODO
                )
                if cti is None:
                    assert ps is not None
                    ps_i = frozenset(predicates.index(p) for p in ps)
                    assert ps_i <= r
                    dual_transitions.append((ps_i, frozenset([j])))
                    r = dual_close_forward(r)
                    assert j in r
                    changes = True
            if changes:
                continue
            # find roots, and try to eliminate them
            # TODO: this is not really correct here, e.g., there can be cycles and then there is no root.
            # we should do something more systematic (e.g., minimal disjunction relative to transitions and substructures)
            assert reachable == close_forward(reachable)
            to_eliminate = frozenset(
                i for i in sorted(live_states - reachable)
                if all(eval_in_state(None, states[i], predicates[j]) for j in sorted(r))
            )
            roots = compute_roots(
                s=to_eliminate,
                pos=reachable,
                ps=[predicates[j] for j in r],
                a=None,
            )
            if len(roots) > 0:
                print(f'forward_explore_from_predicates: trying to eliminate the following {len(roots)} roots: {sorted(roots)}')
            # try to find a new predicate that eliminates a root and is inductive relative to r
            for i in sorted(roots):
                assert i not in reachable, i
                print(f'forward_explore_from_predicates: checking for edge to eliminate states[{i}]')
                res = find_dual_edge([], r, states[i], [states[i] for i in sorted(to_eliminate)], n_ps=0, n_qs=1)
                print(f'forward_explore_from_predicates: done checking for edge to eliminate states[{i}]')
                if res is not None:
                    ps_i = frozenset(add_predicate(p) for p in res[0])
                    qs_i = frozenset(add_predicate(q) for q in res[1])
                    assert ps_i <= r
                    assert len(qs_i) == 1
                    j = list(qs_i)[0]
                    assert not eval_in_state(None, states[i], predicates[j])
                    # TODO: minimize before adding to dual_transitions
                    dual_transitions.append((ps_i, qs_i))
                    r = dual_close_forward(r)
                    assert j in r
                    changes = True
                    break # to prioritize using existing predicates (no stratification, unlike in dual_houdini_frames)
            else:
                if False:
                    # just to find bugs in compute_roots
                    # TODO: run this sometime on all examples
                    for i in sorted(live_states):
                        if i in reachable or not all(eval_in_state(None, states[i], predicates[j]) for j in sorted(r)):
                            continue
                        assert find_dual_edge([], r, states[i], [], n_ps=0, n_qs=1) is None, i

        # here there are no more dual edges that can be added
        inductive_invariant = dual_close_forward(inductive_invariant)
        print(f'Finished forward_explore_from_predicates({sorted(src)}), found {len(r) - n_r} new provable predicates, and added {len(inductive_invariant) - n_inductive_invariant} new predicates to the inductive invariant')

    def find_dual_edge(
            pos: Collection[int], # indices into states that ps must satisfy
            r: Collection[int], # indices into predicates that can be used (assumed invariants)
            goal: Union[State, Predicate], # state to exclude or predicate to prove
            soft_goals: Union[Collection[State], Collection[Predicate]], # more states or predicates to exclude or prove greedily
            n_ps: Optional[int] = None, # None means unbounded, 0 means no such predicates beyond what is in r
            n_qs: int = 1, # for now must be 1
    ) -> Optional[Tuple[Tuple[Predicate,...], Tuple[Predicate,...]]]:
        '''
        May add new reachable states if it finds new initial states
        '''
        nonlocal reachable
        pos = frozenset(pos)
        assert n_qs == 1 # for now only one predicate in q
        assert n_ps in (0, None) # for now we do not support finite bounds, either 0 or unbounded
        if n_ps == 0:
            assert len(pos) == 0
              # for now we don't use n_ps=0 with predicates (although it could make sense, e.g., finding a stronger predicate)
            assert isinstance(goal, State)
            assert all(isinstance(g, State) for g in soft_goals)
        # for now we don't support predicate goals at all
        assert isinstance(goal, State)
        assert all(isinstance(g, State) for g in soft_goals)
        goal_i = states.index(goal)
        soft_goals_i = sorted(states.index(g) for g in soft_goals)  # type: ignore # TODO something better
        print(f'find_dual_edge: starting, pos={sorted(pos)}, r={sorted(r)}, goal=states[{goal_i}], soft_goals=states{soft_goals_i}')
        n_internal_ctis = len(internal_ctis)
        n_reachable = len(reachable)

        ps: List[Predicate] = []
        mp = MultiSubclausesMapICE(
            [maps[goal_i].to_clause(maps[goal_i].all_n)],
            states,
            [],
            True,
        )
        def check_sep(s: Collection[int]) -> Optional[Predicate]:
            s = frozenset(s) | reachable
            res = mp.separate(
                pos=sorted(reachable),
                imp=sorted((i, j) for i, j in chain(transitions, substructure) if i in s and j in s),
                soft_neg=soft_goals_i,
            )
            if res is None:
                return None
            else:
                assert len(res) == mp.m == 1
                return [mp.to_clause(k, res[k]) for k in range(mp.m)][0]
        while True:
            while True: # find a q or discover there is none and learn internal_ctis
                ctis = frozenset(
                    i for i in sorted((live_states | internal_ctis) - reachable)
                    if all(chain(
                            (eval_in_state(None, states[i], predicates[j]) for j in sorted(r)),
                            (eval_in_state(None, states[i], p) for p in ps),
                    ))
                )
                res = check_sep(ctis)
                if res is None:
                    break
                q = res
                # here, q is a predicate such that r /\ ps /\ q |= wp(r /\ ps -> q) has no CTI in live_states | internal_ctis
                # first, check if init |= q, if not, we learn a new initial state
                print(f'find_dual_edge: potential q is ({len(destruct_clause(q)[1])} literals): {q}')
                s = check_initial(solver, q)
                if s is not None:
                    print(f'  this predicate is not initial, learned a new initial state')
                    i = add_state(s, False)
                    reachable |= {i}
                    reachable = close_forward(reachable) # just in case
                    continue
                # now, check if r /\ ps /\ q |= wp(r /\ ps -> q)
                _cti, _ps = check_dual_edge(
                    solver,
                    tuple(chain((predicates[k] for k in sorted(r)), ps)),
                    (q,),
                    # msg='cti?', TODO
                )
                if _cti is None:
                    assert _ps is not None
                    print(f'find_dual_edge: learned {len(internal_ctis) - n_internal_ctis} new internal ctis and {len(reachable) - n_reachable} new reachable states')
                    print(f'find_dual_edge: found new dual edge:')
                    for p in _ps:
                        print(f'  {p}')
                    print(f'  --> {q}')
                    return _ps, (q,)
                else:
                    prestate, poststate = _cti
                    i_pre = add_state(prestate, True)
                    i_post = add_state(poststate, True)
                    assert (i_pre, i_post) not in transitions
                    add_transition(i_pre, i_post)
            # here, we have enough internal_ctis to rule out all possible q's
            assert check_sep(ctis) is None
            if n_ps == 0:
                print(f'find_dual_edge: learned {len(internal_ctis) - n_internal_ctis} new internal ctis and {len(reachable) - n_reachable} new reachable states')
                print(f'find_dual_edge: cannot find dual edge')
                return None
            assert n_ps is None
            # minimize ctis outside of pos and learn a new predicate that separates them from pos
            # TODO: use unsat cores
            soft_neg = ctis - pos
            for i in sorted(ctis - pos):
               if i in ctis and check_sep(ctis - {i}) is None:
                   ctis -= {i}
            assert check_sep(ctis) is None
            to_eliminate = ctis - pos
            print(f'find_dual_edge: looking for a new p that will eliminate some of: {sorted(to_eliminate)}')
            for i in sorted(to_eliminate):
                while True:
                    seed = maps[i].separate(
                        pos=(pos | reachable),
                        neg=[i],
                        soft_neg=soft_neg, # TODO: or to_eliminate ?
                    )
                    if seed is None:
                        break
                    p = maps[i].to_clause(seed)
                    print(f'find_dual_edge: potential p is: {p}')
                    s = check_initial(solver, p)
                    if s is None:
                        break
                    else:
                        print(f'  this predicate is not initial, learned a new initial state')
                        reachable |= {add_state(s, False)}
                        reachable = close_forward(reachable) # just in case
                if seed is not None:
                    ps.append(p)
                    print(f'find_dual_edge: found new p predicate: {p}')
                    break
            else:
                print(f'find_dual_edge: learned {len(internal_ctis) - n_internal_ctis} new internal ctis and {len(reachable) - n_reachable} new reachable states')
                print(f'find_dual_edge: cannot find any new p predicate, so cannot find dual edge')
                return None

    def new_reachable_states() -> None:
        nonlocal live_predicates
        nonlocal reachable
        nonlocal internal_ctis
        reachable = close_forward(reachable)
        live_predicates = frozenset(
            j for j in sorted(live_predicates)
            if all(eval_in_state(None, states[k], predicates[j])
                   for k in sorted(reachable)
            )
        )
        internal_ctis -= reachable

    def new_inductive_invariants() -> None:
        nonlocal live_states
        nonlocal internal_ctis
        nonlocal live_predicates
        nonlocal inductive_invariant
        inductive_invariant = dual_close_forward(inductive_invariant)
        live_states = frozenset(
            i for i in sorted(live_states)
            if all(eval_in_state(None, states[i], predicates[j])
                   for j in sorted(inductive_invariant)
            )
        )
        internal_ctis = frozenset(
            i for i in sorted(internal_ctis)
            if all(eval_in_state(None, states[i], predicates[j])
                   for j in sorted(inductive_invariant)
            )
        )
        # TODO: cleanup unneeded predicates, using more bookkeeping

    def assert_invariants() -> None:
        # for debugging
        assert reachable == close_forward(reachable), sorted(close_forward(reachable) - reachable)
        assert reachable == close_forward(reachable, True), sorted(close_forward(reachable, True) - reachable) # TODO: not sure about this
        assert inductive_invariant == dual_close_forward(inductive_invariant)
        assert live_predicates <= frozenset(
            j for j, p in enumerate(predicates)
            if all(eval_in_state(None, states[k], p)
                   for k in sorted(reachable)
            )
        )
        assert (live_states | internal_ctis) <= frozenset(
            i for i, s in enumerate(states)
            if all(eval_in_state(None, s, predicates[j])
                   for j in sorted(inductive_invariant)
            )
        )
        assert len(internal_ctis & reachable) == 0

    while True:
        # TODO: add a little BMC
        assert_invariants()

        n_inductive_invariant = len(inductive_invariant)
        n_reachable = len(reachable)
        houdini_frames()
        compute_step_frames()
        if len(reachable) > n_reachable:
            print(f'Primal Houdini found {len(reachable) - n_reachable} new reachable states')
            new_reachable_states()
        if len(inductive_invariant) > n_inductive_invariant:
            print(f'Primal Houdini found {len(inductive_invariant) - n_inductive_invariant} new inductive predicates')
            new_inductive_invariants()

        assert_invariants()

        # print status and possibly terminate
        # TODO: output information from dual_frames
        print(f'\n[{datetime.now()}] Current states ({len(live_states)} live, {len(reachable)} reachable, {len(internal_ctis)} internal_ctis):\n' + '-' * 8)
        for i in sorted(live_states | internal_ctis):
            notes: List[str] = []
            if i in live_states:
                notes.append('live')
            if i in reachable:
                notes.append('reachable')
            if i in internal_ctis:
                notes.append('internal_cti')
            note = '(' + ', '.join(notes) + ')'
            print(f'states[{i:3}]{note}:\n{states[i]}\n' + '-' * 80)
        for i in reachable:
            if not cheap_check_implication([states[i].as_onestate_formula(0)], safety):
                print(f'\nFound safety violation by reachable state (states[{i}]).')
                dump_caches()
                return 'UNSAFE'
        print(f'\n[{datetime.now()}] Current transitions ({len(transitions)}) and substructures ({len(substructure)}):')
        for i, j, label in sorted(chain(
                ((i, j, 'transition') for i, j in transitions),
                ((i, j, 'substructure') for i, j in substructure),
        )):
            print(f'  {i:3} -> {j:3} ({label})')
        print(f'\n[{datetime.now()}] Current predicates ({len(live_predicates)} total, {len(inductive_invariant)} proven):')
        for i in sorted(live_predicates):
            max_frame = max(j for j, f in enumerate(frames) if predicates[i] in f)
            assert max_frame < len(frames) - 1 or i in inductive_invariant
            note = (' (invariant)' if i in inductive_invariant else f' ({max_frame + 1})')
            max_frame = max(j for j, f in enumerate(step_frames) if predicates[i] in f)
            assert max_frame < len(step_frames) - 1 or i in inductive_invariant
            if i not in inductive_invariant:
                note += f' ({max_frame + 1})'
            print(f'  predicates[{i:3}]{note}: {predicates[i]}')
        if len(inductive_invariant) > 0 and cheap_check_implication([predicates[i] for i in sorted(inductive_invariant)], safety):
            print('Proved safety!')
            dump_caches()
            return 'SAFE'
        print()

        # try to increase bounds for some states, without discovering
        # new CTIs, and add new predicates

        n_predicates = len(predicates)
        n_live_predicates = len(live_predicates)
        n_inductive_invariant = len(inductive_invariant)
        n_reachable = len(reachable)
        n_live_states = len(live_states)
        n_internal_ctis = len(internal_ctis)
        dual_houdini_frames()
        assert reachable == close_forward(reachable)
        assert inductive_invariant == dual_close_forward(inductive_invariant)
        if len(reachable) > n_reachable:
            print(f'Dual Houdini found {len(reachable) - n_reachable} new reachable states')
            new_reachable_states()
        if len(inductive_invariant) > n_inductive_invariant:
            print(f'Dual Houdini found {len(inductive_invariant) - n_inductive_invariant} new inductive predicates')
            new_inductive_invariants()
        assert_invariants()
        print(f'\nLearned {len(predicates) - n_predicates} new predicates,'
              f'revived {len(live_predicates) - n_live_predicates - len(predicates) + n_predicates} previous predicates,'
              f'learned {len(inductive_invariant) - n_inductive_invariant} new inductive predicates, ',
              f'{len(reachable) - n_reachable} new reachable states,'
              f'{len(live_states) - n_live_states} new live states, '
              f'{len(internal_ctis) - n_internal_ctis} new internal ctis, '
              f'looping\n')
        assert any([
            n_predicates != len(predicates),
            n_live_predicates != len(live_predicates),
            n_inductive_invariant != len(inductive_invariant),
            n_reachable != len(reachable),
            n_live_states != len(live_states),
            n_internal_ctis != len(internal_ctis),
        ])

# class DualEdgeFinder(object):
#     '''Class used to store a map of subclauses of several clauses, and
#     obtain a conjunction of subclauses that satisfy positive,
#     negative, and implication constraints on some given states.
#     '''
#     def __init__(self,
#                  states: List[State],  # assumed to only grow
#                  predicates: List[Expr],  # assumed to only grow
#                  imp: Collection[Tuple[int, int]] = (),
#     ):
#     def find_p_q(self,
#                  reachable: Collection[int] = (), # indices to states
#                  inductive_invariant: Collection[int] = (), # indices to states
#                  pos: Collection[int] = (), # indices to state that must be satisfied by p (dual to a in houdini_frames)
#                  neg: Collection[int] = (), # indices to states, try to make q violate as many of these such that one of the
#                  imp: Collection[Tuple[int, int]] = (), # indices into states, transitions and substructures
#     ) -> Tuple[List[Predicate], List[Predicate]]:
#         '''
#         find a conjunction of subclauses that respects given constraints, and optionally as many soft constraints as possible

#         TODO: to we need an unsat core in case there is no subclause?

#         NOTE: the result must contain a subclause of each top clause, i.e., true cannot be used instead of one of the top clauses
#         '''
#         self._new_states()
#         self._new_predicates()
#         assert all(0 <= i < len(self.states) for i in chain(pos, neg, soft_pos, soft_neg))
#         assert all(0 <= i < len(self.predicates) for i in chain(ps, soft_ps))
#         sep = list(chain(
#             (z3.And(*(self.state_vs[k][i] for k in range(self.m))) for i in sorted(pos)),
#             (z3.Or(*(z3.Not(self.state_vs[k][i]) for k in range(self.m))) for i in sorted(neg)),
#             (z3.Implies(
#                 z3.And(*(self.state_vs[k][i] for k in range(self.m))),
#                 z3.And(*(self.state_vs[k][j] for k in range(self.m))),
#             ) for i, j in sorted(imp)),
#             (self.predicate_vs[i] for i in sorted(ps)),
#         ))
#         soft = list(chain(
#             (z3.And(*(self.state_vs[k][i] for k in range(self.m))) for i in sorted(soft_pos)),
#             (z3.Or(*(z3.Not(self.state_vs[k][i]) for k in range(self.m))) for i in sorted(soft_neg)),
#             (z3.Implies(
#                 z3.And(*(self.state_vs[k][i] for k in range(self.m))),
#                 z3.And(*(self.state_vs[k][j] for k in range(self.m))),
#             ) for i, j in sorted(soft_imp)),
#             (self.predicate_vs[i] for i in sorted(soft_ps)),
#         ))
#         self.solver.push()
#         for c in sep:
#             self.solver.add(c)
#         if len(soft) > 0:
#             assert self.optimize
#             for c in soft:
#                 self.solver.add_soft(c)
#         print(f'Checking MultiSubclausesMapICE.solver... ', end='')
#         res = self.solver.check()
#         print(res)
#         assert res in (z3.unsat, z3.sat)
#         if res == z3.unsat:
#             self.solver.pop()
#             return None
#         # minimize for strongest possible clause
#         # TODO: just use z3's Optimize instead of minimizing manually
#         model = self.solver.model()
#         forced_to_false = [set(
#             i for i, v in enumerate(self.lit_vs[k])
#             if not z3.is_true(model[v])
#         ) for k in range(self.m)]
#         for k in range(self.m):
#             for i in range(self.n[k]):
#                 if i not in forced_to_false[k]:
#                     ki = [(kk, ii) for kk in range(self.m) for ii in forced_to_false[kk]] + [(k, i)]
#                     print(f'Checking MultiSubclausesMapICE.solver... ', end='')
#                     res = self.solver.check(*(z3.Not(self.lit_vs[kk][ii]) for kk, ii in sorted(ki)))
#                     print(res)
#                     assert res in (z3.unsat, z3.sat)
#                     if res == z3.sat:
#                         forced_to_false[k].add(i)
#         ki = [(kk, ii) for kk in range(self.m) for ii in forced_to_false[kk]]
#         assert self.solver.check(*(z3.Not(self.lit_vs[kk][ii]) for kk, ii in sorted(ki))) == z3.sat
#         result = [frozenset(self.all_n[k] - forced_to_false[k]) for k in range(self.m)]
#         self.solver.pop()
#         return result

#     def to_clause(self, k: int, s: Iterable[int]) -> Expr:
#         lits = [self.literals[k][i] for i in sorted(s)]
#         free = set(chain(*(lit.free_ids() for lit in lits)))
#         vs = [v for v in self.variables[k] if v.name in free]
#         return Forall(vs, Or(*lits)) if len(vs) > 0 else Or(*lits)


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
#         print(f'[{datetime.now()}] Current reachable states ({len(reachable)}):')
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
    assert len(set(literals)) == len(literals), clause
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

# This class was made obsolete by SubclausesMapTurbo
# class SeparabilitySubclausesMap(object):
#     '''
#     Class used to store a map of subclauses of a certain clause, and
#     obtain subclauses that are positive and negative on some given
#     states.
#     '''
#     def __init__(self,
#                  top_clause: Expr,
#                  states: List[State],  # assumed to only grow
#                  predicates: List[Expr],  # assumed to only grow
#     ):
#         '''
#         states is assumed to be a list that is increasing but never modified
#         '''
#         self.states = states
#         self.predicates = predicates
#         self.variables, self.literals = destruct_clause(top_clause)
#         self.n = len(self.literals)
#         self.all_n = set(range(self.n))  # used in complement fairly frequently
#         self.solver = z3.Solver()
#         self.lit_vs = [z3.Bool(f'lit_{i}') for i, _ in enumerate(self.literals)]
#         self.state_vs: List[z3.ExprRef] = []
#         self.predicate_vs: List[z3.ExprRef] = []
#         self._new_states()
#         self._new_predicates()

#     def _new_states(self) -> None:
#         self.state_vs.extend(z3.Bool(f's_{i}') for i in range(len(self.state_vs), len(self.states)))

#     def _new_predicates(self) -> None:
#         new = range(len(self.predicate_vs), len(self.predicates))
#         self.predicate_vs.extend(z3.Bool(f'p_{i}') for i in new)
#         for i in new:
#             _, literals = destruct_clause(self.predicates[i])
#             lits = set(literals)
#             if lits <= set(self.literals):
#                 # we need to block up from strict supersets of literals
#                 # TODO: should this be strict or not?
#                 x = ([z3.Not(self.predicate_vs[i])] +
#                      [z3.Not(self.lit_vs[j]) for j in range(self.n) if self.literals[j] in lits]
#                 )
#                 for j in range(self.n):
#                     if self.literals[j] not in lits:
#                         self.solver.add(z3.Or(*x, z3.Not(self.lit_vs[j])))

#     def separate(self,
#                  pos: Collection[int],
#                  neg: Collection[int],
#                  sharp: Collection[int],
#     ) -> Optional[FrozenSet[int]]:
#         '''
#         find a subclause that is positive on pos and negative on neg. pos,neg are indices to self.states.

#         TODO: to we need an unsat core in case there is no subclause?
#         '''
#         self._new_states()
#         self._new_predicates()
#         assert all(0 <= i < len(self.states) for i in chain(pos, neg))
#         assert all(0 <= i < len(self.predicates) for i in sharp)
#         sep = list(chain(
#             (self.state_vs[i] for i in sorted(pos)),
#             (z3.Not(self.state_vs[i]) for i in sorted(neg)),
#             (self.predicate_vs[i] for i in sorted(sharp)),
#         ))
#         while True:
#             res = self.solver.check(*sep)
#             assert res in (z3.unsat, z3.sat)
#             if res == z3.unsat:
#                 return None
#             # minimize for strongest possible clause
#             model = self.solver.model()
#             forced_to_false = set(
#                 i for i, v in enumerate(self.lit_vs)
#                 if not z3.is_true(model[v])
#             )
#             for i in range(self.n):
#                 if i in forced_to_false:
#                     continue
#                 res = self.solver.check(*sep, *(z3.Not(self.lit_vs[j]) for j in sorted(chain(forced_to_false, [i]))))
#                 assert res in (z3.unsat, z3.sat)
#                 if res == z3.sat:
#                     forced_to_false.add(i)
#             assert self.solver.check(*sep, *(z3.Not(self.lit_vs[j]) for j in sorted(forced_to_false))) == z3.sat
#             result = frozenset(self.all_n - forced_to_false)
#             clause = self.to_clause(result)
#             # now check if this clause does the job w.r.t. pos and neg
#             bad = False
#             for i in pos:
#                 if not eval_in_state(None, self.states[i], clause):
#                     # grow and block down
#                     current = result
#                     for j in sorted(self.all_n - result):
#                         if not eval_in_state(None, self.states[i], self.to_clause(current | {j})):
#                             current = current | {j}
#                     self.solver.add(z3.Or(z3.Not(self.state_vs[i]), *(
#                         self.lit_vs[j] for j in sorted(self.all_n - current)
#                     )))
#                     bad = True
#                     break # TODO: should we be eager or lazy here?
#             if bad:
#                 continue # TODO: should we be eager or lazy here?
#             for i in neg:
#                 if eval_in_state(None, self.states[i], clause):
#                     # shrink and block up
#                     current = result
#                     for j in sorted(result):
#                         if eval_in_state(None, self.states[i], self.to_clause(current - {j})):
#                             current = current - {j}
#                     self.solver.add(z3.Or(self.state_vs[i], *(
#                         z3.Not(self.lit_vs[j]) for j in sorted(current)
#                     )))
#                     bad = True
#                     break # TODO: should we be eager or lazy here?
#             if bad:
#                 continue
#             return result

#     def to_clause(self, s: Iterable[int]) -> Expr:
#         lits = [self.literals[i] for i in sorted(s)]
#         free = set(chain(*(lit.free_ids() for lit in lits)))
#         vs = [v for v in self.variables if v.name in free]
#         return Forall(vs, Or(*lits)) if len(vs) > 0 else Or(*lits)


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
        self.maps: List[SubclausesMapTurbo] = []
        self._new_states()

    def _new_states(self) -> None:
        # create new SubclausesMapTurbo's
        for i in range(len(self.maps), len(self.states)):
            cs = as_clauses(Not(self.states[i].as_diagram(0).to_ast()))
            assert len(cs) == 1
            c = cs[0]
            self.maps.append(SubclausesMapTurbo(c, self.states, self.predicates))

    def separate(self,
                 pos: FrozenSet[int],
                 neg: FrozenSet[int],
                 ps: FrozenSet[int],
    ) -> Union[Predicate, Tuple[FrozenSet[int], FrozenSet[int], FrozenSet[int]]]:
        '''Try to find a predicate positive on pos and negative on neg, and
        not implies by any of ps (specifically,the result will never
        be one of ps, even if one of them would otherwise do the job).
        Either return it, or return subsets of pos, neg, ps that
        already make it impossible.

        Note: in case neg is empty, TrueExpr is returned regardless of
        ps, which is an exception to the rule that the result cannot
        be implied by the ps.

        '''
        p: Optional[Predicate] = None
        self._new_states()
        p = self._new_separator(pos, neg, ps)
        if p is not None:
            print(f'Managed to separate: pos={sorted(pos)}, neg={sorted(neg)}, ps={sorted(ps)} with: {p}')
            return p
        else:
            # TODO: it seems that the order of shrinking here significantly changes the runtime (at least of lockserv), should explore this further
            # shrink neg
            for i in sorted(neg):
                if i not in neg:
                    assert False # TODO this can happen once we have "unsat cores" from new_separator
                    continue
                if self._new_separator(pos, neg - {i}, ps) is None:
                    neg = neg - {i}
            # shrink ps
            for i in sorted(ps):
                if i not in ps:
                    assert False # TODO this can happen once we have "unsat cores" from new_separator
                    continue
                if self._new_separator(pos, neg, ps - {i}) is None:
                    ps = ps - {i}
            # shrink pos
            for i in sorted(pos):
                if i not in pos:
                    assert False # TODO this can happen once we have "unsat cores" from new_separator
                    continue
                if self._new_separator(pos - {i}, neg, ps) is None:
                    pos = pos - {i}
            return pos, neg, ps

    def _new_separator(self,
                       pos: FrozenSet[int],
                       neg: FrozenSet[int],
                       ps: FrozenSet[int]
    ) -> Optional[Predicate]:
        # TODO: this should also give "unsat cores"
        assert len(self.states) == len(self.maps) # otherwise we should do self._new_states()
        # print(f'_new_separator: pos={sorted(pos)}, neg={sorted(neg)}, ps={sorted(ps)}')
        if len(neg) == 0:
            return TrueExpr
        if len(pos) == 0:
            return FalseExpr
        for i in sorted(neg):
            # print(f'  trying maps[{i}]')
            mp = self.maps[i]
            p = mp.separate(pos, neg, ps)
            if p is not None:
                return mp.to_clause(p)
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

    # safety = tuple(inv.expr for inv in prog.invs() if inv.is_safety)
    safety = tuple(chain(*(as_clauses(inv.expr) for inv in prog.invs() if inv.is_safety))) # must be in CNF for use in eval_in_state
    def safe(s: State) -> bool:
        return all(eval_in_state(solver, s, p) for p in safety)

    states : List[State] = []
    reachable: List[int] = []
    backward_reachable: List[int] = []
    transitions: List[Tuple[int, int]] = []
    # paths: List[Tuple[int, int]] = []

    def add_state(s: State) -> int:
        if s in states:
            assert False
            # ? return states.index(s)
        i = len(states)
        states.append(s)
        if not safe(s):
            backward_reachable.append(i)
        return i

    predicates: List[Predicate] = []
    # hoare_triples: List[Tuple[FrozenSet[int], FrozenSet[int], FrozenSet[int]]] = []
    sharp_predicates: FrozenSet[int] = frozenset()   # indices into predicates for predicates for current set of sharp predicates
    inductive_invariant: FrozenSet[int] = frozenset()  # indices into predicates for current inductive invariant

    inseparabilities: List[Tuple[FrozenSet[int], FrozenSet[int], FrozenSet[int]]] = []

    def find_inv(k: int) -> Optional[Tuple[FrozenSet[int], List[Tuple[FrozenSet[int], FrozenSet[int]]]]]:
        '''Try to find an invariant using existing sharp predicates + k new ones.

        Result is either None, or (sharp_predicates_used,
        new_predicates) where new_predicates is a list of length k of
        (pos, neg) pairs of indices into states.

        TODO: this is currently not incremental, but it can be made incremental
        '''
        z3s = z3.Solver()
        # basics of encoding into sat
        us = [z3.Bool(f'u_{i}') for i in range(len(predicates))]  # us[i] - predicates[i] is in the invariant
        for i in range(len(predicates)):
            if i in inductive_invariant:
                z3s.add(us[i])
            if i not in sharp_predicates:
                z3s.add(z3.Not(us[i]))

        xs = [[z3.Bool(f'x_{i}_{j}') for j in range(k)] for i in range(len(states))] # xs[i][j] - state i satisfied by new predicate j
        cs = [z3.Bool(f'c_{i}') for i in range(len(states))]  # cs[i] - state i is satisfied by the invariant
        for i, s in enumerate(states):
            z3s.add(cs[i] == z3.And(
                *(z3.Not(us[j]) for j, p in enumerate(predicates) if not eval_in_state(None, s, p)),
                *(xs[i][j] for j in range(k)),
            ))
        # encoding transitions and forward/backward reachable states
        for i in reachable:
            z3s.add(cs[i])
        for i in backward_reachable:  # TODO: this will change when we don't go directly for a safety proof
            z3s.add(z3.Not(cs[i]))
        for i, j in transitions:
            z3s.add(z3.Implies(cs[i], cs[j]))
        # encoding inseparabilities
        for pos, neg, ps in inseparabilities:
            if ps <= sharp_predicates:
                assert len(pos) > 0 and len(neg) > 0
                for j in range(k):
                    z3s.add(z3.Or(*chain(
                        (z3.Not(xs[i][j]) for i in sorted(pos)),
                        (xs[i][j] for i in sorted(neg)),
                    )))
        # now check and bias towards stronger invariants (more predicates, less states satisfied)
        res = z3s.check()
        assert res in (z3.unsat, z3.sat)
        if res == z3.unsat:
            # TODO: return unsat core of states, transitions, and
            # maybe inseparabilities, and use that to see which states
            # should we spend effort on ruling out, or which currently
            # sharp predicates we should spend effort on refuting
            return None
        z3m = z3s.model()
        # grow the set of used predicates
        forced_to_true = set(
            i for i, v in enumerate(us)
            if not z3.is_false(z3m[v])
        )
        assert z3s.check(*(us[j] for j in sorted(forced_to_true))) == z3.sat
        for i in range(len(predicates)):
            if i not in forced_to_true:
                res = z3s.check(*(us[j] for j in sorted(forced_to_true | {i})))
                assert res in (z3.unsat, z3.sat)
                if res == z3.sat:
                    forced_to_true.add(i)
        forced = [us[j] for j in sorted(forced_to_true)]
        assert z3s.check(*forced) == z3.sat
        sharp_predicates_used = frozenset(forced_to_true)
        # shrink the set of states satisfied by the new predicates
        z3m = z3s.model()
        forced_to_false = set(
            (i, j) for i, j in product(range(len(states)), range(k))
            if not z3.is_true(z3m[xs[i][j]])
        )
        assert z3s.check(*forced, *(z3.Not(xs[i][j]) for i, j in sorted(forced_to_false))) == z3.sat
        for j, i in product(range(k), range(len(states))):
            # minimize first predicate, then second predicate, and so on
            if (i, j) not in forced_to_false:
                res = z3s.check(*forced, *(z3.Not(xs[i][j]) for i, j in sorted(forced_to_false | {(i, j)})))
                assert res in (z3.unsat, z3.sat)
                if res == z3.sat:
                    forced_to_false.add((i, j))
        forced.extend(z3.Not(xs[i][j]) for i, j in sorted(forced_to_false))
        assert z3s.check(*forced) == z3.sat
        #  TODO: (pos, neg) in new_predicates should be relaxed if it maintains inductiveness
        new_predicates = [(
            frozenset(i for i in range(len(states)) if (i, j) not in forced_to_false),
            frozenset(i for i in range(len(states)) if (i, j) in forced_to_false),
        ) for j in range(k)]
        return sharp_predicates_used, new_predicates

    def alpha_sharp(states: Collection[State]) -> Sequence[Expr]:
        return sorted(
            alpha_from_predicates(
                solver,
                states,
                [predicates[i] for i in sharp_predicates],
            ),
            key=lambda x: (len(str(x)),str(x))
        )

    def close_forward(s: FrozenSet[int]) -> FrozenSet[int]:
        '''
        return closure under *abstract* post, also adds all known reachable.
        abstract post meanst we consider an inseparability [s], [t], [] as a transition from s to t.
        '''
        r = s | frozenset(reachable)
        changes = True
        while changes:
            changes = False
            # close under transitions
            for i, j in transitions:
                if i in r and j not in r:
                    r |= {j}
                    changes = True
            # close under inseparabilities
            for pos, neg, ps in inseparabilities:
                if len(ps) == 0 and len(neg) == 1 and pos <= r and not neg <= r:
                    assert len(pos) == 1
                    r |= neg
                    changes = True
        return r

    # def close_downward(s: FrozenSet[int], a: Sequence[Predicate]) -> FrozenSet[int]:
    #     a = [p for p in a if all(eval_in_state(None, states[i], p) for i in s)]
    #     return s | frozenset(
    #         i for i in (frozenset(range(len(states))) - s)
    #         if all(eval_in_state(None, states[i], p) for p in a)
    #     )

    def forward_explore_relaxed(a: List[Predicate]) -> List[Predicate]:
        '''Learn new transitions that start at existing states
        (forward_explore) in an attempt to show that no subset of a is
        inductive. Result is the largest subset that cannot be ruled
        out by a CTI that leaves a known state, i.e., like Houdini but
        does not add new "roots", only develops forward reachability
        trees.

        TODO: should use BMC and not just single steps

        '''
        nonlocal reachable
        def alpha_a(states: Collection[State]) -> Sequence[Expr]:
            return alpha_from_predicates(solver, states, a)
        n = -1
        r = frozenset(reachable)
        while len(r) > n:
            n = len(r)
            r = close_forward(r)
            _states, _a, _initials, _transitions = forward_explore(
                # TODO: this does not connect already discovered states
                solver,
                alpha_a,
                [states[i] for i in sorted(r)],
            )
            a = list(_a)
            assert _states[:len(r)] == [states[i] for i in sorted(r)]
            index_map: Dict[int, int] = dict()
            for i in range(len(_states)):
                try:
                    index_map[i] = states.index(_states[i])
                except ValueError:
                    index_map[i] = add_state(_states[i])
            assert [index_map[i] for i in range(len(r))] == sorted(r)
            reachable.extend(index_map[i] for i in _initials)
            for i, j in _transitions:
                ii, jj = index_map[i], index_map[j]
                transitions.append((ii, jj))
            reachable = sorted(close_forward(frozenset(reachable)))
            r = close_forward(r)
            assert frozenset(index_map.values()) <= r
            # close downward
            assert all(eval_in_state(None, states[i], p) for i, p in product(sorted(r), a))
            r = r | frozenset(
                i for i in sorted(frozenset(range(len(states))) - r)
                if all(eval_in_state(None, states[i], p) for p in a)
            )
        return a

    def check_inductive(a: List[Predicate]) -> bool:
        for p in a:
            res = check_two_state_implication(solver, a, p, 'CTI')
            if res is not None:
                prestate, poststate = res
                transitions.append((add_state(prestate), add_state(poststate)))
                return False
        return True

    sm = SeparabilityMap(states, predicates)

    while True:
        print(f'\n[{datetime.now()}] Current states ({len(states)} total, {len(reachable)} reachable, {len(backward_reachable)} backward reachable):\n' + '-' * 80)
        for i in range(len(states)):
            note = (' (reachable)' if i in reachable else
                    ' (backward reachable)' if i in backward_reachable else
                    '')
            print(f'states[{i}]{note}:\n{states[i]}\n' + '-' * 80)
        for i in reachable:
            if not cheap_check_implication([states[i].as_onestate_formula(0)], safety):
                print(f'\nFound safety violation by reachable state (states[{i}]).')
                dump_caches()
                return 'UNSAFE'
        print(f'\n[{datetime.now()}] Current sharp predicates ({len(sharp_predicates)}):')
        for i in sorted(sharp_predicates):
            print(f'  predicates[{i:3}]: {predicates[i]}')

        print(f'\n[{datetime.now()}] Current inseparabilities ({len(inseparabilities)}):')
        for pos, neg, ps in inseparabilities:
            print(f'  {sorted(pos)}, {sorted(neg)}, {sorted(ps)}')

        assert close_forward(frozenset(reachable)) == frozenset(reachable), f'{sorted(close_forward(frozenset(reachable)) - frozenset(reachable))}'
        assert sharp_predicates == frozenset(
            i for i, p in enumerate(predicates)
            if all(eval_in_state(None, states[i], p) for i in reachable)
        )

        # find an invariant with smallest number of new predicates
        # that meets the currently known states, sharp predicates and
        # inseparabilities
        k = 0
        while True:
            while True:
                print(f'\nSearching for consistent inductive invariant with {k} new predicates')
                inv_res = find_inv(k)
                if inv_res is None:
                    print(f'No inductive invariant with {k} predicates, increasing bound')
                    k += 1
                    assert k < 10
                else:
                    sharp_predicates_used, new_predicates = inv_res
                    assert k == len(new_predicates)
                    break
            print(f'Found potential invariant using existing predicates {sorted(sharp_predicates_used)} and {k} new predicates:')
            for pos, neg in new_predicates:
                print(f'  pos={sorted(pos)}, neg={sorted(neg)}')

            # try to realize invariant with new predicates, potentially
            # learning a new inseparability
            new_inseparability = False
            new_sharp_predicates = False
            new_reachable_states = False
            for pos, neg in new_predicates:
                print(f'\nTrying to separate: pos={sorted(pos)}, neg={sorted(neg)}, ps={sorted(sharp_predicates)}')
                p = sm.separate(pos, neg, sharp_predicates)
                if not isinstance(p, Predicate):
                    pos, neg, ps = p
                    print(f'\nLearned new inseparability: pos={sorted(pos)}, neg={sorted(neg)}, ps={sorted(ps)}')
                    inseparabilities.append((pos, neg, ps))
                    new_inseparability = True
                    if len(ps) == 0 and len(neg) == 1 and pos <= frozenset(reachable):
                        assert len(pos) == 1
                        reachable = sorted(close_forward(frozenset(reachable)))
                        sharp_predicates = frozenset(
                            i for i, p in enumerate(predicates)
                            if all(eval_in_state(None, states[i], p) for i in reachable)
                        )
                        print(f'Learned new abstractly reachable state: {list(neg)}')
                        new_reachable_states = True
                    break  # TODO: should we continue rather than break ?
                else:
                    print(f'\nFound separator: {p}')
                    # check if p is sharp or not
                    sharp_p = minimize_clause(p, [states[i] for i in reachable])
                    assert sharp_p not in predicates
                    print(f'Found new sharp predicate: {sharp_p}')
                    sharp_predicates |= {len(predicates)}
                    predicates.append(sharp_p)
                    new_sharp_predicates = True
                    if sharp_p != p:
                        break  # TODO: should we continue rather than break ?
            if new_inseparability and not new_sharp_predicates and not new_reachable_states:
                continue
            else:
                break
        if new_reachable_states:
            continue

        # TODO: figure out exactly when to run the below tests (for
        # safety and inductiveness), e.g. in case where we found an
        # new sharp predicate that stopped the invariant (sharp_p !=
        # p) or in case we found some sharp predicates but also an
        # inseparability

        # we learned new sharp predicates, check the proposed
        # inductive invariant with three checks: initiation, safety,
        # and consecution. We first check safety, and then both
        # initiation and consecution are checked by "generalized
        # Houdini"

        a = [predicates[i] for i in sorted(sharp_predicates)]
        print(f'\nProposed inductive invariant ({len(a)} predicates) is:' if len(a) > 0 else '\nProposed inductive invariant is true')
        for p in sorted(a, key=lambda x: len(str(x))):
            print(f'  {p}')

        # first check if a |= wp(safety)
        print(f'Checking if it implies wp(safety)')
        safety_cti = False
        for p in safety:
            res = check_two_state_implication(solver, a, p, 'safety CTI')
            if res is not None:
                prestate, poststate = res
                if prestate in states:
                    i_pre = states.index(prestate)
                    # assert poststate not in states or (i_pre, states.index(poststate)) not in transitions
                else:
                    i_pre = add_state(prestate)
                if poststate in states:
                    i_post = states.index(poststate)
                else:
                    i_post = add_state(poststate)
                if (i_pre, i_post) not in transitions:
                    transitions.append((i_pre, i_post))
                assert i_post in backward_reachable
                if i_pre not in backward_reachable:
                    backward_reachable.append(i_pre)
                safety_cti = True
                break
        if safety_cti:
            # continue
            pass # maybe there are still some sharp predicates worth ruling out
        else:
            print('Proposed inductive invariant implies wp(safety)')

        # "Generalized Houdini":
        p_cti = None
        while True:
            print(f'\nStarting forward_explore_relaxed with {len(a)} predicates:')
            for p in sorted(a, key=lambda x: len(str(x))):
                print(f'  {p}')
            a = forward_explore_relaxed(a)
            print(f'\nFinished forward_explore_relaxed with {len(a)} predicates:')
            for p in sorted(a, key=lambda x: len(str(x))):
                print(f'  {p}')
            assert p_cti not in a, f'Predicate for which we added a CTI was not eliminated by forward_explore_relaxed: {p_cti}'
            # TODO: if some of the new sharp predicates were already
            # eliminated here on the first iteration, maybe we don't
            # even want to keep them.
            if len(a) == 0:
                break
            print(f'\nChecking for disconnected CTIs')
            for p in a:
                res = check_two_state_implication(solver, a, p, 'CTI')
                if res is not None:
                    prestate, poststate = res
                    i_pre = add_state(prestate)
                    i_post = add_state(poststate)
                    transitions.append((i_pre, i_post))
                    p_cti = p
                    break
            else:
                print(f'No disconnected CTIs found')
                break
        # here, a is inductive, but it may no longer imply safety
        print(f'\n[{datetime.now()}] Current inductive invariant ({len(a)} predicates) is:' if len(a) > 0 else '\n[{datetime.now()}] Current inductive invariant is true')
        for p in sorted(a, key=lambda x: len(str(x))):
            print(f'  {p}')
        if len(a) > 0 and cheap_check_implication(a, safety):
            print('Implies safety!')
            dump_caches()
            return 'SAFE'
        inductive_invariant = frozenset(predicates.index(p) for p in a)
        sharp_predicates = frozenset(
            i for i, p in enumerate(predicates)
            if all(eval_in_state(None, states[i], p) for i in reachable)
        )  # TODO: maybe this should happen earlier, as a result of the first forward_explore_relaxed
        assert close_forward(frozenset(reachable)) == frozenset(reachable)


#
# Here lies a previous (premature) attempt to formalize the primal
# dual algorithm using monotone functions:
#
# Primal Dual Algorithm (WIP)
# class PrimalDualBoundsAlgorithm(object):
#
#
#     '''
#     The primal dual algorithm that tracks bounds and tries to increase the lowest bound
#     '''
#     def __init__(self, solver: Solver):
#         global cache_path
#         cache_path = Path(utils.args.filename).with_suffix('.cache')
#         load_caches()
#
#         self.solver = solver
#         self.prog = syntax.the_program
#         self.sharp = utils.args.sharp
#         self.safety = tuple(inv.expr for inv in self.prog.invs() if inv.is_safety)
#
#         self.states : List[State] = []
#         self.predicates : List[Predicate] = list(chain(*(as_clauses(x) for x in self.safety)))
#         # TODO: we are not taking sharp subclauses of safety, maybe to get
#         # the same effect we can take the powerset (safety is usually not
#         # so many literals)
#
#         self.reachable_states: Set[State] = set()  # subset of states
#         self.invariant_predicates: Set[Predicate]  # subset of predicates
#
#         """
#         self.transition_state: Dict[Tuple[State, State], bool] = dict()  # partial function, is there a transition or not, or maybe we don't know yet
#         self.transition_predicate: Dict[Tuple[FrozenSet[Predicate],State,Predicate], bool] = dict()  # monotone, needs symbolic representation
#         self.path: Dict[Tuple[State, State], bool] = dict()
#         self.hoare:  Dict[Tuple[FrozenSet[Predicate], FrozenSet[Predicate], Predicate], bool] = dict() # monotone partial function, TODO: should be stored differently
#         self.induction: Dict[Tuple[FrozenSet[State], FrozenSet[Predicate], Predicate], bool] = dict() # anti-monotone in states, monotone in predicates, TODO: should be stored differently
#         self.inseperable: Dict[Tuple[FrozenSet[State], FrozenSet[State]], Optional[int]] = dict() # monotone Nat_inf (None represents inf), TODO: should be stored differently
#         assert not self.sharp #  TODO: inseprable does not support sharp, should be made Dict[Tuple[FrozenSet[State], FrozenSet[State], FrozenSet[State]], Optional[int]]
#         # TODO: bounds
#         """
#
#         # version with BMC in mind:
#         NatInf = Optional(int) # None represents infinity, -k represents that the object whose size we are trying to bound actually exists with size k
#         self.transition_state: Dict[Tuple[FrozenSet[Predicate], State, State], NatInf] = defaultdict(int) # lower bound (from BMC) on trace from state to state, all satisfying P
#         self.transition_predicate: Dict[Tuple[FrozenSet[Predicate],State,Predicate], NatInf] = defaultdict(int)  # as above, but for predicate
#
#         self.path: Dict[Tuple[State, State], bool] = dict()
#         self.hoare:  Dict[Tuple[FrozenSet[Predicate], FrozenSet[Predicate], Predicate], bool] = dict() # monotone partial function, TODO: should be stored differently
#         self.induction: Dict[Tuple[FrozenSet[State], FrozenSet[Predicate], Predicate], bool] = dict() # anti-monotone in states, monotone in predicates, TODO: should be stored differently
#         self.inseperable: Dict[Tuple[FrozenSet[State], FrozenSet[State]], Optional[int]] = dict() # monotone Nat_inf (None represents inf), TODO: should be stored differently
#         assert not self.sharp #  TODO: inseprable does not support sharp, should be made Dict[Tuple[FrozenSet[State], FrozenSet[State], FrozenSet[State]], Optional[int]]
#         # TODO: bounds
#
#         # Taking the monotone perspective even futrther:
#         states = self.states
#         predicates = self.predicates
#         T = ((predicates,'-'), (states,'+'), (states,'+'), (states,'|'), (NatInf, '+'))
#         # T[G,S,A,B,k] = is there a state t in B that is reachable
#         # from A by a trace of states that satisfy G, and
#         # uses states from S "for free", but < k new states
#         I = ((states,'-'), (predicates,'+'), (predicates,'+'), (predicates,'|'), (NatInf, '+'))
#         # I[R,D,P,Q,k] = is there a predicate q in Q that is provable
#         # from P by an inductive invariant that is satisfied by R, and
#         # uses predicates from D "for free", but at < k new predicates
#         H = ((predicates,'+'), (states, '-'), (predicates,'+'), (predicates,'+'), (NatInf, '-'))
#         # H[G,S,P,Q,k] = is the Hoare triple {/\P} ((TRANS \cup paths(S)) \cap [G]x[G])^i {\/Q} valid for all i < k
#         U = ((states,'-'), (predicates,'+'), (states,'+'), (states,'|'), (NatInf, '-'))
#         # U[R,D,A,B,k] = is any invariant with at most k predicates
#         # not from D that is satisfied by R and has no CTI in A also
#         # satisfied by at least one state in B
#         W = ((states,'+'), (states,'+'), (NatInf, '+'))
#         # W[A,B,k] = is there a conjunction of < k predicates that are satisfied by A and not satisfied by any state in B
#         HH =  ((predicates,'+'), (states, '-'), (predicates,'+'), (predicates,'+'), (NatInf, '-'), (NatInf, '-'))
#
#     def check_transition_state_state(self, s: State, t: State) -> None:
#         assert (s, t) not in self.transition
#         res = check_two_state_implication_all_transitions(
#             self.solver,
#             [s.as_onestate_formula(0)],
#             Not(t.as_onestate_formula(0)),
#         )
#         if res is None:
#             self.transition[(s, t)] = False
#             print('No transition between states:')
#             print('prestate:')
#             print('-'*80 + '\n' + str(s) + '\n' + '-'*80)
#             print('postistate:')
#             print('-'*80 + '\n' + str(t) + '\n' + '-'*80)
#             # TODO: maybe here we should learn a Hoare triple that
#             # excludes this transition
#         else:
#             self.transition[(s, t)] = True
#             print('Found transition between states:')
#             print('prestate:')
#             print('-'*80 + '\n' + str(s) + '\n' + '-'*80)
#             print('postistate:')
#             print('-'*80 + '\n' + str(t) + '\n' + '-'*80)
#             # for debugging:
#             z3m, _ = res
#             prestate = Model.from_z3([KEY_OLD], z3m)
#             poststate = Model.from_z3([KEY_NEW, KEY_OLD], z3m)
#             assert isomorphic_states(self.solver, s, prestate)
#             assert isomorphic_states(self.solver, t, poststate)
#
#     def check_transition_state_predicate(self, G: Sequence[Predicate], s: State, q: Predicate) -> None:
#         assert (s, q) not in self.transition
#         res = check_two_state_implication(self.solver, s, Implies(And(*G), q))
#         if res is None:
#             self.transition[(s, q)] = False
#         else:
#             prestate, poststate = res
#             self.transition[(s, q)] = True
#             self.states.append(poststate)
#             self.transition[(s, poststate)] = True


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

    # repeated_houdini_bounds
    s = subparsers.add_parser('pd-repeated-houdini-bounds', help='Run the repeated Houdini algorith in the proof space')
    s.set_defaults(main=repeated_houdini_bounds)
    result.append(s)

    # cdcl_state_bounds
    s = subparsers.add_parser('pd-cdcl-state-bounds', help='Run the "CDCL state bounds" algorithm')
    s.set_defaults(main=cdcl_state_bounds)
    result.append(s)

    # cdcl_predicate_bounds
    s = subparsers.add_parser('pd-cdcl-predicate-bounds', help='Run the "CDCL predicate bounds" algorithm')
    s.set_defaults(main=cdcl_predicate_bounds)
    result.append(s)

    # cdcl_invariant
    s = subparsers.add_parser('pd-cdcl-invariant', help='Run the "CDCL over invariants" algorithm')
    s.set_defaults(main=cdcl_invariant)
    result.append(s)

    # primal_dual_houdini
    s = subparsers.add_parser('pd-primal-dual-houdini', help='Run the "Primal-Dual" algorithm')
    s.set_defaults(main=primal_dual_houdini)
    result.append(s)

    for s in result:
        s.add_argument('--unroll-to-depth', type=int, help='Unroll transitions to given depth during exploration')
        s.add_argument('--cpus', type=int, help='Number of CPUs to use in parallel')

    return result
