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
import multiprocessing.connection
from contextlib import nullcontext
import random
from random import randint
import queue
from datetime import datetime, timedelta
from hashlib import sha1
from dataclasses import dataclass
import gzip

from syntax import *
from logic import *
from translator import Z3Translator

from typing import TypeVar, Iterable, FrozenSet, Union, Callable, Generator, Set, Optional, cast, Type, Collection, TYPE_CHECKING, AbstractSet

A = TypeVar('A')
# form: https://docs.python.org/3/library/itertools.html#itertools-recipes
def powerset(iterable: Iterable[A]) -> Iterator[Tuple[A, ...]]:
    'powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)'
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))


PDState = Trace  # TODO: change this to logic.State!
Predicate = Expr


def unpack_cti(z3model: z3.ModelRef, *, keep_prestate_in_poststate: bool = False) -> Tuple[PDState, PDState]:
    '''
    Unpack a z3model with two states to (prestate, poststate).

    Both prestate and poststate are are currently logic.Trace objects,
    but in the future they will be logic.State
    objects. keep_prestate_in_poststate maintains legacy compatability
    with representing a poststate by a 2-state trace where the first
    one (index 0) is the poststate and the second one (index 1) is the
    prestate.
    '''
    prestate = Z3Translator.model_to_trace(z3model, 1)
    if keep_prestate_in_poststate:
        poststate = Z3Translator.model_to_trace(z3model, 2)._as_trace((1, 0))  # TODO: eliminate Trace._as_trace
    else:
        poststate = Z3Translator.model_to_trace(z3model, 2)._as_trace((1,))  # TODO: eliminate Trace._as_trace
    return prestate, poststate


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
                assert v == m.as_state(0).eval(p), f'{p}\n=========\n{m}'
            # utils.exit(0)

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


# # Here's a hacky way to eval a possibly-quantified z3 expression.
# # This function only works if e is either quantifier free, or has exactly one quantifier
# # (with arbitrarily many bound vars) at the root of the expression.  For example, this
# # function will not work on the conjunction of two universally quantified clauses.
# def eval_quant(m: z3.ModelRef, e: z3.ExprRef) -> bool:
#     def ev(e: z3.ExprRef) -> bool:
#         ans = m.eval(e)#, model_completion=True)
#         assert z3.is_bool(ans)
#         assert z3.is_true(ans) or z3.is_false(ans), f'{m}\n{"="*80}\n{e}\n{"="*80}\n{ans}'
#         return bool(ans)
#     if not isinstance(e, z3.QuantifierRef):
#         return ev(e)
#     else:
#         q = all if e.is_forall() else any
#         return q(ev(z3.substitute_vars(e.body(), *tup)) for tup in product(*(
#             m.get_universe(e.var_sort(i)) for i in range(e.num_vars() - 1, -1, -1) # de Bruijn
#         )))

# def eval_clause_in_state(
#         clause: Expr,
#         state: PDState,
# ) -> bool:
#     variables, literals = destruct_clause(clause)
#     def ev(values: Sequence[str], lit: Expr) -> bool:
#         # TODO: rewrite this with James, this is a hacky partial implementation of first-order logic semantics for class Trace (written on a plane from Phoenix to SF)
#         assert len(variables) == len(values)
#         consts_and_vars: Dict[str, str] = dict(chain(
#             ((var.name, val) for var, val in zip(variables, values)),
#             ((d.name, val) for d, val in state.immut_const_interps.items()),
#             ((d.name, val) for d, val in state.const_interps[0].items()),
#         ))
#         functions: Dict[str, Dict[Tuple[str,...], str]] = dict(
#             (d.name, dict((tuple(args), val) for args, val in func))
#             for d, func in chain(state.immut_func_interps.items(), state.func_interps[0].items())
#         )
#         relations: Dict[str, Dict[Tuple[str,...], bool]] = dict(
#             (d.name, dict((tuple(args), val) for args, val in func))
#             for d, func in chain(state.immut_rel_interps.items(), state.rel_interps[0].items())
#         )
#         def get_term(t: Expr) -> str:
#             if isinstance(t, Id):
#                 assert t.name in consts_and_vars, f'{t.name}\n' + '='*80 + f'\n{state}\n'
#                 return consts_and_vars[t.name]
#             elif isinstance(t, AppExpr):
#                 assert t.callee in functions, f'{t.callee}\n' + '='*80 + f'\n{state}\n'
#                 return functions[t.callee][tuple(get_term(a) for a in t.args)]
#             else:
#                 assert False, t
#         if isinstance(lit, Bool):
#             return lit.val
#         elif isinstance(lit, UnaryExpr):
#             assert lit.op == 'NOT', lit
#             return not ev(values, lit.arg)
#         elif isinstance(lit, BinaryExpr):
#             assert lit.op in ('EQUAL', 'NOTEQ'), lit
#             eq = get_term(lit.arg1) == get_term(lit.arg2)
#             return eq if lit.op == 'EQUAL' else not eq
#         elif isinstance(lit, AppExpr):
#             return relations[lit.callee][tuple(get_term(a) for a in lit.args)]
#         elif isinstance(lit, Id):
#             # nullary relation
#             assert lit.name in relations, f'{lit.name}\n' + '='*80 + f'\n{state}\n'
#             return relations[lit.name][()]
#         else:
#             assert False, lit
#     universes = []
#     for v in variables:
#         assert isinstance(v.sort, UninterpretedSort), v
#         if v.sort.decl is not None and v.sort.decl in state.univs:
#             assert v.sort.name == v.sort.decl.name, v
#             universes.append(state.univs[v.sort.decl])
#         else:
#             # assert False, v # TODO: ask James why does this happen
#             ds = [d for d in state.univs if d.name == v.sort.name]
#             assert len(ds) == 1, v
#             universes.append(state.univs[ds[0]])
#     n = reduce(lambda x, y: x * y, [len(u) for u in universes], 1)
#     # print(f'eval_clause_in_state: iterating over {n} instantiations... ', end='')
#     result = all(any(ev(tup,lit) for lit in literals) for tup in product(*universes))
#     # print(f'done.')
#     return result

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
    t = s.get_translator(1)
    with s.new_frame():
        for e in hyps:
            s.add(t.translate_expr(e))
        for e in concs:
            with s.new_frame():
                s.add(z3.Not(t.translate_expr(e)))
                res = s.check()
                assert res in (solver.sat, solver.unsat), res
                if res != z3.unsat:
                    return False
    return True


_cache_eval_in_state : Dict[Any,Any] = dict(h=0,m=0)
def eval_in_state(s: Optional[Solver], m: PDState, p: Expr) -> bool:
    # if s is None:
    #     s = get_solver()
    cache = _cache_eval_in_state
    k = (m, p)
    if k not in cache:
        res = m.as_state(0).eval(p)
        assert isinstance(res, bool)
        cache[k] = res

        # Older ways:
        #
        # cache[k] = eval_clause_in_state(p, m)
        #
        # if m.z3model is not None:
        #     try:
        #         cache[k] = eval_quant(m.z3model, s.get_translator((m.keys[0],)).translate_expr(p))
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

_cache_initial: List[PDState] = []
# TODO: could also cache expressions already found to be initial
def check_initial(solver: Solver, p: Expr) -> Optional[Trace]:
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
        s = Z3Translator.model_to_trace(z3m, 1)
        _cache_initial.append(s)
        print(f'Found new initial state violating {p}:')
        print('-'*80 + '\n' + str(s) + '\n' + '-'*80)
        return s
    return None


def is_substructure(s: Union[PDState, State], t: Union[PDState, State]) -> bool:
    '''Returns true if s is a sub structure of t'''
    if isinstance(s, PDState):
        s = s.as_state(0)
    if isinstance(t, PDState):
        t = t.as_state(0)
    if not s.maybe_substructure(t):
        return False
    diag_s = Diagram(s).to_ast()
    diag_t = Diagram(t).to_ast()
    if diag_s == diag_t:
        return True
    return cheap_check_implication([diag_t], [diag_s])


_cache_two_state_implication : Dict[Any,Any] = dict(h=0,r=0)
_cache_transitions: List[Tuple[PDState,PDState]] = []
def isomorphic_states(solver: Solver, s: PDState, t: PDState) -> bool:
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
) -> Optional[Tuple[Trace, Trace]]:
    if s is None:
        s = Solver()
    if seed is not None:
        # print(f'PID={os.getpid()} setting z3 seed to {seed}')
        # z3.set_param('smt.random_seed', seed) -- this probably needs to be called before creating the solver
        # TODO: figure out if this is a good way to set the seed
        s.z3solver.set(seed=seed)  # type: ignore  # TODO: fix typing

    # print(f'[{datetime.now()}] [PID={os.getpid()}] check_two_state_implication_all_transitions: starting')
    res = check_two_state_implication_all_transitions(s, old_hyps, new_conc, minimize)
    # print(f'[{datetime.now()}] [PID={os.getpid()}] check_two_state_implication_all_transitions: done')
    if seed is not None:
        print(f'PID={os.getpid()} z3 returned {"unsat" if res is None else "sat"}')
    if res is None:
        return None
    else:
        z3m, _ = res
        return unpack_cti(z3m, keep_prestate_in_poststate=True)
def check_two_state_implication_multiprocessing(
        s: Solver,
        old_hyps: Iterable[Expr],
        new_conc: Expr,
        minimize: Optional[bool] = None,
) -> Optional[Tuple[Trace, Trace]]:
    # this function uses multiprocessing to start multiple solvers
    # with different random seeds and return the first result obtained
    print(f'[{datetime.now()}] check_two_state_implication_multiprocessing: starting')
    try:
        if utils.args.cpus is None or utils.args.cpus == 1 or True:
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
    finally:
        print(f'[{datetime.now()}] check_two_state_implication_multiprocessing: done')
    assert False
def check_two_state_implication(
        s: Solver,
        precondition: Union[Iterable[Expr], PDState],
        p: Expr,
        msg: str = 'transition',
        minimize: Optional[bool] = None,
) -> Optional[Tuple[PDState,PDState]]:
    prog = syntax.the_program
    # inits = tuple(init.expr for init in prog.inits())
    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # must be in CNF for use in eval_in_state

    if not isinstance(precondition, PDState):
        precondition = tuple(precondition)
    k = (precondition, p)
    cache = _cache_two_state_implication
    if k not in cache:
        if utils.args.cache_only:
            print(f'loudly describing this unexpected cache miss for predicate {p} on precondition:')
            if isinstance(precondition, PDState):
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
            if ((isomorphic_states(s, prestate, precondition) if isinstance(precondition, PDState) else
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
                [precondition.as_onestate_formula(0)] if isinstance(precondition, PDState) else precondition,
                p,
                minimize
            )
            if res is None:
                cache[k] = None
            else:
                if utils.args.cache_only_discovered:
                    print(f'loudly describing this unexpected cache miss for predicate {p} on precondition:')
                    if isinstance(precondition, PDState):
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
                        if isinstance(precondition, PDState):
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
            if isinstance(precondition, PDState):
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
def check_dual_edge_old(
        # TODO: this is very inefficient since it lets z3 handle the disjunction, keeping for reference, and should remove after thorough validation of the new version
        s: Solver,
        ps: Tuple[Expr,...],
        qs: Tuple[Expr,...],
        msg: str = 'cti',
) -> Tuple[Optional[Tuple[PDState, PDState]], Optional[Tuple[Expr,...]]]:
    '''
    this checks if ps /\ qs |= wp(ps -> qs)
    note it does not check if init |= qs, but for now we assert it
    '''
    prog = syntax.the_program
    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # must be in CNF for use in eval_in_state
    k = (ps, qs)
    cache: Dict[Any,Any] = dict(h=0,r=0) # so that we don't interfere with the new version
    print(f'check_dual_edge_old: starting to check the following edge ({len(ps)}, {len(qs)}):')
    for p in ps:
        print(f'  {p}')
    print('  -->')
    for q in qs:
        print(f'  {q}')
    assert cheap_check_implication(inits, ps)
    assert cheap_check_implication(inits, qs)
    def check(ps_i: FrozenSet[int], minimize: bool) -> Optional[Tuple[z3.ModelRef, DefinitionDecl]]:
        _ps = [ps[i] for i in sorted(ps_i)]
        print(f'check_dual_edge_old: calling z3... ', end='')
        res =  check_two_state_implication_all_transitions(
            s,
            chain(_ps, qs),
            Implies(And(*_ps), And(*qs)), # TODO: when we have 10-20 qs, z3 completely chokes (e.g. sharded-kv.pd-primal-dual-houdini.121761d.seed-0.log), we should reimplement check_dual_edge with many calls to a single solver instance
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
                print(f'check_dual_edge_old: found previous {msg} violating dual edge')
                # print('-'*80 + '\n' + str(poststate) + '\n' + '-'*80)
                break
        else:
            ps_i = frozenset(range(len(ps)))
            res = check(ps_i, True)
            if res is not None:
                if utils.args.cache_only_discovered:
                    assert False
                prestate, poststate = unpack_cti(res[0], keep_prestate_in_poststate=True)
                print(f'check_dual_edge_old: found new {msg} violating dual edge')
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
                print(f'check_dual_edge_old: found new valid dual edge:')
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
            print(f'check_dual_edge_old: found cached {msg} violating dual edge')
        else:
            print(f'check_dual_edge_old: found cached valid dual edge:')
            for p in ps:
                print(f'  {p}')
            print('  -->')
            for q in qs:
                print(f'  {q}')
        cache['h'] += 1

    return cache[k]
# Here is the less stupid version (reusing code from find_dual_backward_transition, much refactoring needed):
# TODO: cache valid dual edges like we cache transitions
def check_dual_edge_multiprocessing_helper(
        ps: Tuple[Expr,...],
        qs: Tuple[Expr,...],
        i_transition: int,
        i_q: int,
        minimize: bool,
        save_smt2: bool = False,
) -> Optional[Tuple[PDState, PDState]]:
    prog = syntax.the_program
    trans = list(prog.transitions())[i_transition]
    s = Solver()
    seed = randint(0, 10**6)
    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_multiprocessing_helper: i_transition={i_transition}, i_q={i_q}: setting z3 seed to {seed}')
    # TODO: not sure any of these has any actual effect
    z3.set_param('smt.random_seed',seed)
    z3.set_param('sat.random_seed',seed)
    s.z3solver.set(seed=seed) # type: ignore
    s.z3solver.set(random_seed=seed) # type: ignore
    t = s.get_translator(2)
    for q in qs:
        s.add(t.translate_expr(q))
    s.add(t.translate_expr(trans.as_twostate_formula(prog.scope)))
    for i, p in enumerate(ps):
        s.add(t.translate_expr(p))
        s.add(t.translate_expr(New(p)))
    q = qs[i_q]
    s.add(z3.Not(t.translate_expr(New(q))))
    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_multiprocessing_helper: i_transition={i_transition}, i_q={i_q}: checking')
    if save_smt2:
        smt2 = s.z3solver.to_smt2()
        fn = f'{sha1(smt2.encode()).hexdigest()}.smt2'
        print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_multiprocessing_helper: i_transition={i_transition}, i_q={i_q}: saving smt2 to {fn} ({len(smt2)} bytes)')
        open(fn, 'w').write(smt2)
    z3res = s.check()
    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_multiprocessing_helper: i_transition={i_transition}, i_q={i_q}: got {z3res}')
    assert z3res in (z3.sat, z3.unsat)
    if z3res == z3.unsat:
        return None
    else:
        prestate, poststate = unpack_cti(s.model(minimize=minimize))
        print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_multiprocessing_helper: i_transition={i_transition}, i_q={i_q}: found model')
        return prestate, poststate
def check_dual_edge_multiprocessing(
        ps: Tuple[Expr,...],
        qs: Tuple[Expr,...],
        minimize: bool,
) -> Optional[Tuple[Trace, Trace]]:
    # this function uses multiprocessing to start multiple solvers for different transitions and qs
    prog = syntax.the_program
    n_transitions = len(list(prog.transitions()))
    n = n_transitions * len(qs)
    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_multiprocessing: starting {n} processes')
    with multiprocessing.Pool(processes=n) as pool:
        results = []
        for i_q, i_transition in product(range(len(qs)), range(n_transitions)):
            results.append(pool.apply_async(
                check_dual_edge_multiprocessing_helper,
                (ps, qs, i_transition, i_q, minimize),
            ))
        while True:
            not_ready = []
            for r in results:
                r.wait(1)
                if r.ready():
                    res = r.get(1)
                    if res is not None:
                        print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_multiprocessing: got a SAT result, returning')
                        return res  # the context manager of pool will terminate the processes
                    else:
                        pass # unsat result, keep waiting for others
                else:
                    not_ready.append(r)
            if len(not_ready) == 0:
                print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_multiprocessing: got all UNSAT results, returning')
                return None
            else:
                results = not_ready
    assert False
# see: https://mypy.readthedocs.io/en/latest/common_issues.html#using-classes-that-are-generic-in-stubs-but-not-at-runtime
if TYPE_CHECKING:
    CheckDualEdgeQueue = multiprocessing.Queue[Optional[Tuple[PDState, PDState]]]  # this is only processed by mypy
else:
    CheckDualEdgeQueue = multiprocessing.Queue  # this is not seen by mypy but will be executed at runtime.
def check_dual_edge_multiprocessing_seeds_helper(
        ps: Tuple[Expr,...],
        qs: Tuple[Expr,...],
        i_transition: int,
        i_q: int,
        minimize: bool,
        save_smt2: bool,
        result_queue: CheckDualEdgeQueue,
) -> None:
    # time.sleep(randint(0,120)) # for debugging
    result_queue.put(check_dual_edge_multiprocessing_helper(ps, qs, i_transition, i_q, minimize, save_smt2))
_luby_sequence: List[int] = [1]
def luby(i: int) -> int:
    global _luby_sequence
    # return the (i+1)'th element of the Luby sequence (so i=0 is the first element)
    while not i < len(_luby_sequence):
        _luby_sequence += _luby_sequence
        _luby_sequence.append(2 * _luby_sequence[-1])
    return _luby_sequence[i]
def check_dual_edge_multiprocessing_seeds(
        ps: Tuple[Expr,...],
        qs: Tuple[Expr,...],
        minimize: bool,
) -> Optional[Tuple[Trace, Trace]]:
    # this function uses multiprocessing to start multiple solvers for
    # different transitions, qs, and random seeds, and restarts the solvers using a Luby sequence
    prog = syntax.the_program
    n_transitions = len(list(prog.transitions()))
    n_cpus = utils.args.cpus if utils.args.cpus is not None else 1
    # list of: process, result_queue, deadline, i_transition, i_q
    running: List[Tuple[multiprocessing.Process, CheckDualEdgeQueue, datetime, int, int]] = []
    # map from (i_transition, i_q) to number of attempts spent on it (note that attempt i takes Luby[i] time)
    # once an unsat result is obtained, the (i_transition, i_q) are removed
    tasks: Dict[Tuple[int, int], int] = dict(
        ((i_transition, i_q), 0)
        for i_transition in range(n_transitions)
        for i_q in range(len(qs))
    )
    t0 = timedelta(seconds=60) # the base unit for timeouts is 60 seconds (i.e., Luby sequence starts at 60 seconds)
    try:
        while True:
            # first, see if we got new results
            for process, result_queue, deadline, i_transition, i_q in running:
                try:
                    res = result_queue.get_nowait() # this causes no results to be obtained even after a sat result was printed from the process
                except queue.Empty:
                    # print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_multiprocessing_seeds: no result yet from PID={process.pid}, i_transition={i_transition}, i_q={i_q}')
                    continue
                if res is not None:
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_multiprocessing_seeds: got a SAT result from PID={process.pid}, i_transition={i_transition}, i_q={i_q}, returning')
                    return res  # the finally will terminate all remaining processes
                else:
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_multiprocessing_seeds: got an UNSAT result for i_transition={i_transition}, i_q={i_q}')
                    tasks.pop((i_transition, i_q), None)
            if len(tasks) == 0:
                print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_multiprocessing_seeds: got all UNSAT results, returning')
                return None

            # second, terminate processes whose timeout has passed or whose task already returned unsat
            now = datetime.now()
            still_running = []
            for process, result_queue, deadline, i_transition, i_q in running:
                if now > deadline:
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_multiprocessing_seeds: terminating process with PID={process.pid}, i_transition={i_transition}, i_q={i_q} due to timeout')
                    process.terminate()
                    process.join()
                elif (i_transition, i_q) not in tasks:
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_multiprocessing_seeds: terminating process with PID={process.pid}, i_transition={i_transition}, i_q={i_q} due to unsat result')
                    process.terminate()
                    process.join()
                else:
                    still_running.append((process, result_queue, deadline, i_transition, i_q))
            running = still_running

            # third, start new processes
            while len(running) < n_cpus:
                minimum = min(tasks.values())
                for i_transition, i_q in sorted(tasks.keys()):
                    if tasks[i_transition, i_q] == minimum:
                        break
                assert tasks[i_transition, i_q] == minimum
                timeout = t0 * luby(tasks[i_transition, i_q])
                tasks[i_transition, i_q] += 1
                result_queue = CheckDualEdgeQueue()
                process = multiprocessing.Process(
                    target=check_dual_edge_multiprocessing_seeds_helper,
                    args=(ps, qs, i_transition, i_q, minimize,
                          tasks[i_transition, i_q] == n_cpus + 1, # on the (n_cpus + 1)'th attempt, save to smt2 for later analysis
                          result_queue),
                )
                deadline = datetime.now() +  timeout
                print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_multiprocessing_seeds: starting new process for i_transition={i_transition}, i_q={i_q} with a timeout of {timeout.total_seconds()} seconds')
                running.append((process, result_queue, deadline, i_transition, i_q))
                process.start()

            # fourth, wait for a bit
            time.sleep(0.1)
        assert False
    finally:
        # terminate all running processeses
        for process, result_queue, deadline, i_transition, i_q in running:
            print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_multiprocessing_seeds: terminating process with PID={process.pid}')
            process.terminate()
            process.join()
        assert len(multiprocessing.active_children()) == 0
def check_dual_edge(
        s: Solver,
        ps: Tuple[Expr,...],
        qs: Tuple[Expr,...],
        msg: str = 'cti',
) -> Tuple[Optional[Tuple[PDState, PDState]], Optional[Tuple[Expr,...]]]:
    '''
    this checks if ps /\ qs |= wp(ps -> qs)
    note it does not check if init |= qs, but for now we assert it
    '''
    prog = syntax.the_program
    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # must be in CNF for use in eval_in_state
    k = (ps, qs)
    cache = _cache_dual_edge
    print(f'[{datetime.now()}] check_dual_edge: starting')
    print(f'[{datetime.now()}] check_dual_edge: starting to check the following edge ({len(ps)}, {len(qs)}):')
    for p in ps:
        print(f'  {p}')
    print('  -->')
    for q in qs:
        print(f'  {q}')
    #production# assert cheap_check_implication(inits, ps)
    #production# assert cheap_check_implication(inits, qs)
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
                print(f'[{datetime.now()}] check_dual_edge: found previous {msg} violating dual edge')
                # print('-'*80 + '\n' + str(poststate) + '\n' + '-'*80)
                break
        else:
            # now we really have to check, use a specilized solver, with one solver per transition (older version that uses a single solver is available in commit c533c48)
            cti_solvers: List[Solver] = []
            for trans in prog.transitions():
                _cti_solver = Solver()
                t = _cti_solver.get_translator(2)
                for q in qs:
                    _cti_solver.add(t.translate_expr(q))
                _cti_solver.add(t.translate_expr(trans.as_twostate_formula(prog.scope)))
                p_indicators = [z3.Bool(f'@p_{i}') for i in range(len(ps))]
                for i, p in enumerate(ps):
                    _cti_solver.add(z3.Implies(p_indicators[i], t.translate_expr(p)))
                    _cti_solver.add(z3.Implies(p_indicators[i], t.translate_expr(New(p))))
                q_indicators = [z3.Bool(f'@q_{i}') for i in range(len(qs))]
                for i, q in enumerate(qs):
                    _cti_solver.add(z3.Implies(q_indicators[i], z3.Not(t.translate_expr(New(q)))))
                cti_solvers.append(_cti_solver)
            def check(ps_seed: FrozenSet[int], minimize: bool) -> Optional[Tuple[PDState, PDState]]:
                if True:
                    # use multiprocessing
                    res = check_dual_edge_multiprocessing_seeds(
                        ps=tuple(ps[i] for i in sorted(ps_seed)),
                        qs=qs,
                        minimize=minimize,
                    )
                    if res is not None and minimize:
                        # TODO: should we put it in the cache anyway? for now not
                        prestate, poststate = res
                        _cache_transitions.append((prestate, poststate))
                        for state in (prestate, poststate):
                            if all(eval_in_state(None, state, p) for p in inits):
                                _cache_initial.append(state)
                                # TODO: maybe we should first try to get (from Z3) a transition where the prestate is initial
                    return res
                else:
                    # no multiprocessing
                    for q_indicator, (cti_solver, trans) in product(q_indicators, zip(cti_solvers, prog.transitions())):
                        print(f'[{datetime.now()}] check_dual_edge: testing {q_indicator}, transition {trans.name}')
                        indicators = tuple(chain(
                            [q_indicator],
                            (p_indicators[i] for i in sorted(ps_seed)),
                        ))
                        z3res = cti_solver.check(indicators)
                        assert z3res in (z3.sat, z3.unsat)
                        print(f'[{datetime.now()}] check_dual_edge: {z3res}')
                        if z3res == z3.unsat:
                            continue
                        prestate, poststate = unpack_cti(cti_solver.model(indicators, minimize))
                        if minimize:
                            # TODO: should we put it in the cache anyway? for now not
                            _cache_transitions.append((prestate, poststate))
                            for state in (prestate, poststate):
                                if all(eval_in_state(None, state, p) for p in inits):
                                    _cache_initial.append(state)
                            # TODO: maybe we should first try to get (from Z3) a transition where the prestate is initial
                        return prestate, poststate
                    return None
            ps_i = frozenset(range(len(ps)))
            res = check(ps_i, True)
            if res is not None:
                if utils.args.cache_only_discovered:
                    assert False
                prestate, poststate = res
                print(f'[{datetime.now()}] check_dual_edge: found new {msg} violating dual edge')
                cache[k] = ((prestate, poststate), None)
            else:
                # minimize ps_i
                # TODO: maybe use unsat cores
                print(f'[{datetime.now()}] check_dual_edge: minimizing ps')
                for i in sorted(ps_i, reverse=True): # TODO: reverse or not?
                    if i in ps_i and check(ps_i - {i}, False) is None:
                        ps_i -= {i}
                _ps = tuple(ps[i] for i in ps_i)
                print(f'[{datetime.now()}] check_dual_edge: done minimizing ps')
                print(f'[{datetime.now()}] check_dual_edge: found new valid dual edge:')
                for p in _ps:
                    print(f'  {p}')
                print('  -->')
                for q in qs:
                    print(f'  {q}')
                cache[k] = (None, _ps)

            if False:
                # just validation vs the old implementation
                old = check_dual_edge_old(s, ps, qs, msg='validation-cti')
                assert (old[0] is None) == (cache[k][0] is None)
                assert (old[1] is None) == (cache[k][1] is None)

        if len(cache) % 100 == 1:
            # dump_caches()
            print(f'_cache_dual_edge length is {len(cache)}, h/r is {cache["h"]}/{cache["r"]}')

    else:
        cti, ps = cache[k]
        if cti is not None:
            print(f'[{datetime.now()}] check_dual_edge: found cached {msg} violating dual edge')
        else:
            print(f'[{datetime.now()}] check_dual_edge: found cached valid dual edge:')
            for p in ps:
                print(f'  {p}')
            print('  -->')
            for q in qs:
                print(f'  {q}')
        cache['h'] += 1

    print(f'[{datetime.now()}] check_dual_edge: done')
    return cache[k]

#
# check_dual_edge_optimize and friends
#

@dataclass(frozen=True)
class HoareQuery:
    '''Class that represents a check during check_dual_edge_optimize'''
    p: FrozenSet[int]
    q_pre: Tuple[FrozenSet[int],...]
    q_post: Tuple[FrozenSet[int],...]
    cardinalities: Tuple[Optional[int],...]
    i_transition: int
    # maybe use in repr/str: f'precondition_seed={[sorted(x) for x in precondition_seed]}, postcondition_seed={[sorted(x) for x in postcondition_seed]}, cardinalities={cardinalities}'
    def __post_init__(self) -> None:
        assert len(self.q_pre) == len(self.q_post)
        assert len(self.cardinalities) == 0 # for now
    def __str__(self) -> str:
        def str_seed(seed: Tuple[FrozenSet[int], ...]) -> str:
            return str([sorted(x) for x in seed]).replace(' ', '')

        return f'({sorted(self.p)}, {str_seed(self.q_pre)}, {str_seed(self.q_post)}, {self.i_transition})'
    def __le__(self, other: HoareQuery) -> bool:
        # TODO: maybe the order should be reversed?
        return (
            (self.i_transition == other.i_transition) and
            len(self.q_pre) == len(other.q_pre) and
            len(self.q_post) == len(other.q_post) and
            len(self.cardinalities) == len(other.cardinalities) and
            (self.p >= other.p) and
            all(x <= y for x, y in zip(self.q_pre, other.q_pre)) and
            all(x >= y for x, y in zip(self.q_post, other.q_post)) and
            all(
                (y is None) or (x is not None and x <= y)
                for x, y in zip(self.cardinalities, other.cardinalities)
            )
        )
    def __ge__(self, other: HoareQuery) -> bool:
        return other <= self
    def __lt__(self, other: HoareQuery) -> bool:
        return self != other and self <= other
    def __gt__(self, other: HoareQuery) -> bool:
        return self != other and other <= self
    def strengthen_p(self, d: AbstractSet[int]) -> HoareQuery:
        return HoareQuery(
            p=self.p | d,
            q_pre=self.q_pre,
            q_post=self.q_post,
            cardinalities=self.cardinalities,
            i_transition=self.i_transition,
        )
    def weaken_p(self, d: AbstractSet[int]) -> HoareQuery:
        return HoareQuery(
            p=self.p - d,
            q_pre=self.q_pre,
            q_post=self.q_post,
            cardinalities=self.cardinalities,
            i_transition=self.i_transition,
        )
    def strengthen_q_pre(self, k: int, d: AbstractSet[int]) -> HoareQuery:
        q_pre = list(self.q_pre)
        q_pre[k] -= d
        return HoareQuery(
            p=self.p,
            q_pre=tuple(q_pre),
            q_post=self.q_post,
            cardinalities=self.cardinalities,
            i_transition=self.i_transition,
        )
    def weaken_q_pre(self, k: int, d: AbstractSet[int]) -> HoareQuery:
        q_pre = list(self.q_pre)
        q_pre[k] |= d
        return HoareQuery(
            p=self.p,
            q_pre=tuple(q_pre),
            q_post=self.q_post,
            cardinalities=self.cardinalities,
            i_transition=self.i_transition,
        )
    def strengthen_q_post(self, k: int, d: AbstractSet[int]) -> HoareQuery:
        q_post = list(self.q_post)
        q_post[k] -= d
        return HoareQuery(
            p=self.p,
            q_pre=self.q_pre,
            q_post=tuple(q_post),
            cardinalities=self.cardinalities,
            i_transition=self.i_transition,
        )
    def weaken_q_post(self, k: int, d: AbstractSet[int]) -> HoareQuery:
        q_post = list(self.q_post)
        q_post[k] |= d
        return HoareQuery(
            p=self.p,
            q_pre=self.q_pre,
            q_post=tuple(q_post),
            cardinalities=self.cardinalities,
            i_transition=self.i_transition,
        )
    def replace_cardinality(self, k: int, n: Optional[int]) -> HoareQuery:
        cardinalities = list(self.cardinalities)
        cardinalities[k] = n
        return HoareQuery(
            p=self.p,
            q_pre=self.q_pre,
            q_post=self.q_post,
            cardinalities=tuple(cardinalities),
            i_transition=self.i_transition,
        )
    def replace_transition(self, i_transition: int) -> HoareQuery:
        return HoareQuery(
            p=self.p,
            q_pre=self.q_pre,
            q_post=self.q_post,
            cardinalities=self.cardinalities,
            i_transition=i_transition,
        )

# see: https://mypy.readthedocs.io/en/latest/common_issues.html#using-classes-that-are-generic-in-stubs-but-not-at-runtime
if TYPE_CHECKING:
    # this is only processed by mypy
    T = Tuple[
        HoareQuery,
        bool, # True means valid, False means invalid
        Optional[Tuple[PDState, PDState]], # optional CTI for invalid, but not required
    ]
    CheckDualEdgeOptimizeQueue = multiprocessing.Queue[T]
    CheckDualEdgeOptimizeJoinableQueue = multiprocessing.JoinableQueue[T]
else:
    # this is not seen by mypy but will be executed at runtime.
    CheckDualEdgeOptimizeQueue = multiprocessing.Queue
    CheckDualEdgeOptimizeJoinableQueue = multiprocessing.JoinableQueue

def assert_valid_hq(
    ps: Tuple[Expr,...],
    top_clauses: Tuple[Expr,...],
    hq: HoareQuery,
) -> None:
    mp = MultiSubclausesMapICE(top_clauses, [], []) # only used to get clauses from seeds
    assert all(0 <= i < len(ps) for i in hq.p), (hq.p, list(map(str, ps)))
    assert len(hq.q_pre) == mp.m, (hq.q_pre, mp.m, list(map(str, top_clauses)))
    assert len(hq.q_post) == mp.m, (hq.q_post, mp.m, list(map(str, top_clauses)))
    for k in range(mp.m):
        assert all(0 <= i < mp.n[k] for i in hq.q_pre[k]), (k, hq.q_pre[k], mp.m, mp.n, list(map(str, top_clauses)))
        assert all(0 <= i < mp.n[k] for i in hq.q_post[k]), (k, hq.q_post[k], mp.m, mp.n, list(map(str, top_clauses)))

def check_dual_edge_optimize_multiprocessing_helper(
        ps: Tuple[Expr,...],
        top_clauses: Tuple[Expr,...],
        hq: HoareQuery,
        produce_cti: bool, # if False, we do not get models from the solver
        optimize: bool, # if False, we do not try to optimize an invalid Hoare triple
        whole_clauses: bool, # if True, only try the empty clause or the entire top_clause (used in find_dual_backward_transition)
        use_cvc4: bool,
        save_smt2: bool, # TODO: move to separate function
        q1: CheckDualEdgeOptimizeJoinableQueue,
        q2: CheckDualEdgeOptimizeQueue,
        join_q1: bool = True, # can be set to false if not running in separate process
) -> None:
    greeting = f'[PID={os.getpid()}] check_dual_edge_optimize_multiprocessing_helper: use_cvc4={use_cvc4}, hq={hq}'

    if use_cvc4:
        minimize = utils.args.cvc4_minimize_models
    else:
        minimize = True
    try:
        assert_valid_hq(ps, top_clauses, hq)

        def send_result(hq: HoareQuery, valid: bool, cti: Optional[Tuple[PDState, PDState]] = None) -> None:
            assert cti is None or not valid
            if not produce_cti:
                cti = None
            q1.put((hq, valid, cti))
        def validate_cti(prestate: PDState, poststate: PDState) -> None:
            # TODO: remove this once we trust the code enough
            return
            assert all(eval_in_state(None, prestate,  p) for p in ps), f'{greeting}: {(ps, top_clauses, hq, s.debug_recent())}'
            assert all(eval_in_state(None, poststate, p) for p in ps), f'{greeting}: {(ps, top_clauses, hq, s.debug_recent())}'
            assert all(eval_in_state(None, prestate,  mp.to_clause(k, hq.q_pre[k])) for k in range(mp.m)), f'{greeting}: {(ps, top_clauses, hq, s.debug_recent())}'
            assert all(not eval_in_state(None, poststate, mp.to_clause(k, hq.q_post[k])) for k in range(mp.m)), f'{greeting}: {(ps, top_clauses, hq, s.debug_recent())}'
        known_unsats: List[HoareQuery] = []
        def recv_unsats() -> None:
            while True:
                try:
                    hq, valid, cti = q2.get_nowait()
                except queue.Empty:
                    break
                assert valid and cti is None
                known_unsats.append(hq)
        def known_to_be_unsat(hq: HoareQuery) -> bool:
            if any(len(x) == 0 for x in hq.q_pre):
                return True
            recv_unsats()
            return any(
                hq <= unsat_hq
                for unsat_hq in known_unsats
            )
        recv_unsats()
        prog = syntax.the_program
        mp = MultiSubclausesMapICE(top_clauses, [], []) # only used to get clauses from seeds
        # TODO: better logging, maybe with meaningful process names
        def get_solver(hq: HoareQuery) -> Tuple[Solver, Z3Translator]:
            s = Solver(use_cvc4=use_cvc4)
            seed = randint(0, 10**6)
            if not use_cvc4:
                # print(f'[{datetime.now()}] {greeting}: setting z3 seed to {seed}')
                # TODO: not sure any of these has any actual effect
                z3.set_param('smt.random_seed',seed)
                z3.set_param('sat.random_seed',seed)
                s.z3solver.set(seed=seed) # type: ignore
                s.z3solver.set(random_seed=seed) # type: ignore
            else:
                # print(f'[{datetime.now()}] {greeting}: using cvc4 (random seed set by run_cvc4.sh)')
                pass
            t = s.get_translator(2)
            # add transition relation
            s.add(t.translate_expr(list(prog.transitions())[hq.i_transition].as_twostate_formula(prog.scope)))
            # add ps
            for i in sorted(hq.p):
                s.add(t.translate_expr(ps[i]))
                s.add(t.translate_expr(New(ps[i])))
            # add precondition constraints
            for k in range(mp.m):
                s.add(t.translate_expr(mp.to_clause(k, hq.q_pre[k])))
            # add postcondition constraints, note we must violate all clauses (the selection of which one to violate is represented by making the others empty
            for k in range(mp.m):
                if len(hq.q_post[k]) > 0:
                    s.add(z3.Not(t.translate_expr(New(mp.to_clause(k, hq.q_post[k])))))
            return s, t
        s, t = get_solver(hq)
        if save_smt2:
            smt2 = s.z3solver.to_smt2()
            fn = f'{sha1(smt2.encode()).hexdigest()}.smt2'
            print(f'[{datetime.now()}] {greeting}: saving smt2 to {fn} ({len(smt2)} bytes)')
            open(fn, 'w').write(smt2)
            # TODO: we should actually exit here, i.e., make saving to smt2 a separate function
        print(f'[{datetime.now()}] {greeting}: checking input queury')
        z3res = s.check()
        print(f'[{datetime.now()}] {greeting}: got {z3res}' + (', optimizing cti' if z3res == z3.sat and optimize else ''))
        assert z3res in (z3.sat, z3.unsat)
        if z3res == z3.unsat:
            send_result(hq, True)
            # we do not try to optimize unsats, as this isn't marco, we only optimize one direction
            # TODO: maybe we should do marco? also note that the unsat is only for this transition

            # to safe some forking (e.g., in cache there are 15 transitions), we other transitions in random order so that we may switch
            # TODO: we can also check violations of other conjuncts of q, but this would require changing the interface
            n_transitions = len(list(prog.transitions()))
            worklist = [
                hq.replace_transition(i_transition)
                for i_transition in range(n_transitions)
                if i_transition != hq.i_transition
            ]
            worklist = [other_hq for other_hq in worklist if not known_to_be_unsat(other_hq)]
            random.shuffle(worklist)
            print(f'[{datetime.now()}] {greeting}: input was unsat, trying {len(worklist)} other transitions')
            for other_hq in worklist:
                if known_to_be_unsat(other_hq):
                    continue
                s, t = get_solver(other_hq)
                z3res = s.check()
                assert z3res in (z3.sat, z3.unsat)
                if z3res == z3.unsat:
                    send_result(other_hq, True)
                else:
                    # we found a cti, now continue us usual and optimize it
                    hq = other_hq
                    break
            else:
                # all transitions are unsat, return
                return

        assert s.check() == z3.sat

        if not optimize and not produce_cti:
            # just report that the Hoare triple is invalid
            send_result(hq, False)
            return

        # get model
        prestate, poststate = unpack_cti(s.model(minimize=minimize))
        validate_cti(prestate, poststate)

        if not optimize:
            # send model without optimizing it
            send_result(hq, False, (prestate, poststate))
            return

        # optimize from model and send result (but only optimize top priority, i.e., active_post_qs)
        active_post_qs = [k for k in range(mp.m) if len(hq.q_post[k]) > 0] # we will first try to weaken these
        if not whole_clauses:
            for k in active_post_qs:
                for j in sorted(mp.all_n[k] - hq.q_post[k]):
                    if not eval_in_state(None, poststate, mp.to_clause(k, hq.q_post[k] | {j})):
                        # print(f'[{datetime.now()}] {greeting}: weakening postcondition from model k={k}, j={j}')
                        hq = hq.weaken_q_post(k, {j})
        else:
            # in this case, we optimize all post_qs from model
            for k in range(mp.m):
                if not eval_in_state(None, poststate, mp.to_clause(k, mp.all_n[k])):
                    # print(f'[{datetime.now()}] {greeting}: weakening postcondition from model k={k} (whole clauses)')
                    hq = hq.weaken_q_post(k, mp.all_n[k])

        validate_cti(prestate, poststate)
        send_result(hq, False, (prestate, poststate))

        # optimize to get an optimal cti
        # first try for the post-state to violate weaker subclauses of top_clauses[active_post_qs]
        # then try for the post-state to violate non-empty subclauses of the other top_clauses
        # then try for the pre-state to satisfy stronger subclauses of top_clauses
        # TODO: lastly, minimize the model (i.e., cardinalities)
        # TODO: maybe we should minimize cardinalities before the other top_clauses, as it could lead to larger models
        # print(f'[{datetime.now()}] {greeting}: optimizing postcondition')
        for k in chain(active_post_qs, (kk for kk in range(mp.m) if kk not in active_post_qs)): # TODO: random shuffle?
            if not whole_clauses:
                to_try = [frozenset([i]) for i in sorted(mp.all_n[k] - hq.q_post[k])]
            else:
                to_try = [] if hq.q_post[k] == mp.all_n[k] else [mp.all_n[k]]
            while len(to_try) > 0:
                d = random.choice(to_try)
                to_try.remove(d)
                assert not d <= hq.q_post[k]
                hq_try = hq.weaken_q_post(k, d)
                if known_to_be_unsat(hq_try):
                    continue
                s.push()
                s.add(z3.Not(t.translate_expr(New(mp.to_clause(k, hq_try.q_post[k])))))
                # print(f'[{datetime.now()}] {greeting}: trying to weaken postcondition k={k}, d={sorted(d)}')
                z3res = s.check()
                # print(f'[{datetime.now()}] {greeting}: got {z3res}')
                assert z3res in (z3.sat, z3.unsat)
                if z3res == z3.unsat:
                    send_result(hq_try, True)
                else:
                    # print(f'[{datetime.now()}] {greeting}: weakening postcondition k={k}, d={sorted(d)}')
                    hq = hq_try
                    prestate, poststate = unpack_cti(s.model(minimize=minimize))
                    validate_cti(prestate, poststate)
                    for dd in to_try:
                        if not eval_in_state(None, poststate, mp.to_clause(k, hq.q_post[k] | dd)):
                            # print(f'[{datetime.now()}] {greeting}: weakening postcondition from model k={k}, dd={sorted(dd)}')
                            hq = hq.weaken_q_post(k, dd)
                            to_try.remove(dd)
                    # TODO: weaken from model for other k's?
                    validate_cti(prestate, poststate)
                    send_result(hq, False, (prestate, poststate))
                s.pop()
            # print(f'[{datetime.now()}] {greeting}: optimal q_post[{k}]: {sorted(hq.q_post[k])}')
            s.add(z3.Not(t.translate_expr(New(mp.to_clause(k, hq.q_post[k])))))
            assert s.check() == z3.sat
        # print(f'[{datetime.now()}] {greeting}: optimizing precondition')
        for k in range(mp.m):  # TODO: random shuffle?
            if not whole_clauses:
                to_try = [frozenset([i]) for i in sorted(hq.q_pre[k])]
            else:
                to_try = []
            while len(to_try) > 0:
                d = random.choice(to_try)
                to_try.remove(d)
                assert d <= hq.q_pre[k]
                hq_try = hq.strengthen_q_pre(k, d)
                if known_to_be_unsat(hq_try):
                    continue
                s.push()
                s.add(t.translate_expr(mp.to_clause(k, hq_try.q_pre[k])))
                # print(f'[{datetime.now()}] {greeting}: trying to strengthen precondition k={k}, d={sorted(d)}')
                z3res = s.check()
                # print(f'[{datetime.now()}] {greeting}: got {z3res}')
                assert z3res in (z3.sat, z3.unsat)
                if z3res == z3.unsat:
                    send_result(hq_try, True)
                else:
                    # print(f'[{datetime.now()}] {greeting}: strengthening precondition k={k}, d={sorted(d)}')
                    hq = hq_try
                    prestate, poststate = unpack_cti(s.model(minimize=minimize))
                    validate_cti(prestate, poststate)
                    for dd in to_try:
                        if eval_in_state(None, prestate, mp.to_clause(k, hq.q_pre[k] - dd)):
                            # print(f'[{datetime.now()}] {greeting}: strengthening precondition from model k={k}, dd={sorted(dd)}')
                            hq = hq.strengthen_q_pre(k, dd)
                            to_try.remove(dd)
                    # TODO: strengthen other k's from model?
                    validate_cti(prestate, poststate)
                    send_result(hq, False, (prestate, poststate))
                s.pop()
            # print(f'[{datetime.now()}] {greeting}: optimal q_pre[{k}]: {sorted(hq.q_pre[k])}')
            s.add(t.translate_expr(mp.to_clause(k, hq.q_pre[k])))
            assert s.check() == z3.sat
        # print(f'[{datetime.now()}] {greeting}: found optimal cti')
    finally:
        if join_q1:
            q1.join()
        print(f'[{datetime.now()}] {greeting}: finished and joined q1, returning')

@dataclass
class RunningProcess:
    process: multiprocessing.Process
    q1: CheckDualEdgeOptimizeJoinableQueue
    q2: CheckDualEdgeOptimizeQueue
    deadline: datetime
    hq: HoareQuery
    use_cvc4: bool
    def terminate(self) -> None:
        '''Terminate the process if it's still alive (using SIGTERM).

        Makes sure to close the queues and join their thread so it
        does not get pipe errors.
        '''
        if not self.process.is_alive():
            # no need to close and join the queues here, and doing so
            # leads to a rare deadlock
            self.process.join()
        else:
            # need to close and join the queues here, otherwise we'll
            # get pipe errors from the queues' threads.
            self.q1.close()
            self.q2.close()
            # it seems this can lead to deadlocks even if self.process.is_alive returned true. maybe its enough just to close the queue? (question is will we get pipe errors)
            # self.q1.join_thread()
            # self.q2.join_thread()
            self.process.terminate()
            self.process.join()

def check_dual_edge_optimize_find_cti(
        ps: Tuple[Expr, ...],
        top_clauses: Tuple[Expr, ...],
        q_seed: Tuple[FrozenSet[int], ...],
        whole_clauses: bool, # if True, only try the empty clause or the entire top_clause (used in find_dual_backward_transition)
) -> Optional[Tuple[PDState, PDState]]:
    '''
    this uses multiprocessing to check a dual edge, and get an
    optimized cti in case the edge is not valid

    this function uses multiprocessing to start multiple solvers for
    different transitions, qs, and random seeds, and restarts the solvers using a Luby sequence

    '''
    print(f'[{datetime.now()}] check_dual_edge_optimize_find_cti: starting')
    assert len(top_clauses) == len(q_seed)
    mp = MultiSubclausesMapICE(top_clauses, [], []) # only used to get clauses from seeds
    prog = syntax.the_program
    n_transitions = len(list(prog.transitions()))
    n_cpus = utils.args.cpus if utils.args.cpus is not None else 1
    n_cpus = max(n_cpus, 2) # we need at least 2 processes or we will block on the last one that found a model
    t0 = timedelta(seconds=60) # the base unit for timeouts is 60 seconds (i.e., Luby sequence starts at 60 seconds)

    known_unsats: List[HoareQuery] = []
    def known_to_be_unsat(hq: HoareQuery) -> bool:
        return any(len(x) == 0 for x in hq.q_pre) or any(
            hq <= unsat_hq
            for unsat_hq in known_unsats
        )

    active_queries = [
        HoareQuery(
            p=frozenset(range(len(ps))),
            q_pre=q_seed,
            q_post=tuple(q_seed[k] if k == i_q else frozenset() for k in range(mp.m)),
            cardinalities=(),
            i_transition=i_transition,
        )
        for i_transition in range(n_transitions)
        for i_q in range(mp.m)
    ]
    if not whole_clauses:
        # greedily try to jump to the top of q_post
        active_queries += [
            HoareQuery(
                p=frozenset(range(len(ps))),
                q_pre=q_seed,
                q_post=tuple(mp.all_n[k] if k == i_q else frozenset() for k in range(mp.m)),
                cardinalities=(),
                i_transition=i_transition,
            )
            for i_transition in range(n_transitions)
            for i_q in range(mp.m)
            if q_seed[i_q] != mp.all_n[i_q]
        ]

    print(f'[{datetime.now()}] check_dual_edge_optimize_find_cti: initially with {len(active_queries)} active queries')

    running: List[RunningProcess] = [] # list of currently running processes

    # details about the best SAT result we got so far:
    current_cti: Optional[Tuple[PDState, PDState]] = None
    current_hq: Optional[HoareQuery] = None
    current_sat_rp: Optional[RunningProcess] = None

    # map (hq, use_cvc4) to number of attempts spent on it (note that attempt i takes Luby[i] time)
    # nothing is ever removed from tasks, and active_queries is used to maintain the active ones
    tasks: Dict[Tuple[HoareQuery, bool], int] = defaultdict(int)

    try:
        while True:
            # see if we got new results
            n_known_unsats = len(known_unsats) # to later send the new onces
            worklist = list(running)
            any_news = False
            while len(worklist) > 0:
                rp = worklist[0]
                try:
                    hq, valid, cti = rp.q1.get_nowait()
                    rp.q1.task_done()
                except queue.Empty:
                    worklist = worklist[1:]
                    continue
                any_news = True
                assert hq <= rp.hq.replace_transition(hq.i_transition) # we may get a cti for another transition, and we allow it
                assert (valid and cti is None) or (not valid and cti is not None)
                if valid:
                    # got new unsat result
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_find_cti: got an UNSAT result from PID={rp.process.pid} for hq={hq}, use_cvc4={rp.use_cvc4}')
                    known_unsats.append(hq)
                elif current_hq is not None and not hq.replace_transition(0) < current_hq.replace_transition(0):
                    # got a new cti but it's not better than our current best model (ignoring the transition), so we ignore it
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_find_cti: got a SAT result from PID={rp.process.pid} that we discard (hq={hq}, use_cvc4={rp.use_cvc4})')
                else:
                    # the new cti is strictly better than our current
                    # cti. this is a big deal. the process that found
                    # it becomes not subject to timeout, all the other
                    # processes will get killed, and new queries will
                    # get started
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_find_cti: got a SAT result from PID={rp.process.pid} that is better than what we had (hq={hq}, use_cvc4={rp.use_cvc4})')
                    current_cti = cti
                    current_hq = hq
                    current_sat_rp = rp
                    active_queries = []
                    # first, see if there is a way to weaken the postcondition where it was non-trivial before
                    for k in range(mp.m):
                        if len(hq.q_post[k]) == 0:
                            continue
                        if not whole_clauses:
                            to_try = [frozenset([i]) for i in sorted(mp.all_n[k] - hq.q_post[k])]
                        else:
                            to_try = [] if hq.q_post[k] == mp.all_n[k] else [mp.all_n[k]]
                        for d in to_try:
                            assert not d <= hq.q_post[k]
                            for i_transition in range(n_transitions):
                                new_hq = hq.weaken_q_post(k, d).replace_transition(i_transition)
                                if not known_to_be_unsat(new_hq):
                                    active_queries.append(new_hq)
                    # second, weaken the postcondition elsewhere
                    if len(active_queries) == 0:
                        for k in range(mp.m):
                            if len(hq.q_post[k]) != 0:
                                continue
                            if not whole_clauses:
                                to_try = [frozenset([i]) for i in sorted(mp.all_n[k] - hq.q_post[k])]
                            else:
                                to_try = [] if hq.q_post[k] == mp.all_n[k] else [mp.all_n[k]]
                            for d in to_try:
                                assert not d <= hq.q_post[k]
                                for i_transition in range(n_transitions):
                                    new_hq = hq.weaken_q_post(k, d).replace_transition(i_transition)
                                    if not known_to_be_unsat(new_hq):
                                        active_queries.append(new_hq)
                    # third, strengthen the precondition
                    if len(active_queries) == 0 and not whole_clauses:
                        for k in range(mp.m):
                            for i in sorted(hq.q_pre[k]):
                                for i_transition in range(n_transitions):
                                    new_hq = hq.strengthen_q_pre(k, {i}).replace_transition(i_transition)
                                    if not known_to_be_unsat(new_hq):
                                        active_queries.append(new_hq)

            # filter using unknown unsats and possibly return
            active_queries = [hq for hq in active_queries if not known_to_be_unsat(hq)]
            if current_hq is not None:
                active_queries = [hq for hq in active_queries if hq.replace_transition(0) < current_hq.replace_transition(0)] # only keep queries for which a SAT result would be better than the current CTI
            if len(active_queries) == 0:
                # we are done
                print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_find_cti: no more active queries, returning {"cti" if current_cti is not None else "unsat"}')
                print(f'[{datetime.now()}] check_dual_edge_optimize_find_cti: done')
                return current_cti
            elif any_news:
                print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_find_cti: {len(active_queries)} more active queries, carrying on')
                # for hq in active_queries:
                #    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_find_cti:     {hq}')
                # print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_find_cti: carrying on')

            # kill processes that timed out or whose query is no longer active (except for current_sat_rp - the last process to return a model)
            now = datetime.now()
            still_running = []
            for rp in running:
                if not rp.process.is_alive():
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_find_cti: process with PID={rp.process.pid} terminated')
                    rp.terminate()
                    assert rp.process.exitcode == 0, rp.process.exitcode
                elif rp is current_sat_rp:
                    # this processes is protected, and its task doesn't need to be in tasks
                    still_running.append(rp)
                elif all(rp.hq.replace_transition(i_transition) not in active_queries for i_transition in range(n_transitions)): # rp will also try other transitions
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_find_cti: terminating process with PID={rp.process.pid}, hq={rp.hq}, use_cvc4={rp.use_cvc4} due to another result')
                    rp.terminate()
                elif now > rp.deadline:
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_find_cti: terminating process with PID={rp.process.pid}, hq={rp.hq}, use_cvc4={rp.use_cvc4} due to timeout')
                    rp.terminate()
                else:
                    still_running.append(rp)
            running = still_running

            # send new_unsats to everyone whose still running
            for hq in known_unsats[n_known_unsats:]:
                for rp in running:
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_find_cti: sending new unsat to process with PID={rp.process.pid}')
                    rp.q2.put((hq, True, None))

            # start new processes
            active_tasks = list(product(
                active_queries, # hq
                [False, True], # use_cvc4
            ))
            while len(running) < n_cpus:
                task_to_run = min(active_tasks, key=tasks.__getitem__)
                hq, use_cvc4 = task_to_run
                timeout = t0 * luby(tasks[task_to_run])
                tasks[task_to_run] += 1
                q1 = CheckDualEdgeOptimizeJoinableQueue()
                q2 = CheckDualEdgeOptimizeQueue()
                args = (
                    ps,
                    top_clauses,
                    hq,
                    True, # produce_cti
                    True, # optimize
                    whole_clauses,
                    use_cvc4,
                    not use_cvc4 and tasks[task_to_run] == n_cpus + 1, # on the (n_cpu + 1)'th attempt, save to smt2 for later analysis
                    q1,
                    q2,
                )
                # assert_valid_hq(*args[:3])
                if TYPE_CHECKING: # trick to get typechecking for check_dual_edge_optimize_multiprocessing_helper
                    check_dual_edge_optimize_multiprocessing_helper(*args)
                process = multiprocessing.Process(
                    target=check_dual_edge_optimize_multiprocessing_helper,
                    args=args,
                )
                deadline = datetime.now() +  timeout
                print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_find_cti: starting new process for hq={hq}, use_cvc4={use_cvc4} with a timeout of {timeout.total_seconds()} seconds')
                rp = RunningProcess(
                    process,
                    q1,
                    q2,
                    deadline,
                    hq,
                    use_cvc4,
                )
                for hq in known_unsats: # put known_unsats in q2 before starting the process
                    rp.q2.put((hq, True, None))
                process.start()
                running.append(rp)

            # wait for a bit
            # print('\n\nsleeping for a bit\n\n')
            # time.sleep(0.1)
            # print('\n\nwaking up again\n\n')

            # wait until we have new results, or until the next deadline expires
            earliest_deadline = min(
                (rp.deadline for rp in running if rp is not current_sat_rp),
                default=None,
            )
            seconds = (0.1 if earliest_deadline is None else
                       (earliest_deadline - datetime.now()).total_seconds())
            seconds = max(0.1, seconds)
            print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_find_cti: waiting for news with a timeout of {seconds} seconds')
            multiprocessing.connection.wait(
                [rp.q1._reader for rp in running], # type: ignore
                timeout=seconds,
            )
        assert False
    finally:
        # terminate all running processeses
        for rp in running:
            print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_find_cti: terminating process with PID={rp.process.pid}')
            rp.terminate()
        assert len(multiprocessing.active_children()) == 0

def check_dual_edge_optimize_minimize_ps(
        ps: Tuple[Expr, ...],
        top_clauses: Tuple[Expr, ...],
        q_seed: Tuple[FrozenSet[int], ...],
) -> FrozenSet[int]:
    '''
    this uses multiprocessing to minimize the ps required for the given valid dual edge

    this function uses multiprocessing to start multiple solvers for
    different transitions, ps, and random seeds, and restarts the solvers using a Luby sequence

    '''
    assert len(top_clauses) == len(q_seed)
    if len(ps) == 0:
        return frozenset()
    print(f'[{datetime.now()}] check_dual_edge_optimize_minimize_ps: starting')
    print(f'[{datetime.now()}] check_dual_edge_optimize_minimize_ps: minimizing {len(ps)} ps')
    mp = MultiSubclausesMapICE(top_clauses, [], []) # only used to get clauses from seeds
    prog = syntax.the_program
    n_ps = len(ps)
    n_transitions = len(list(prog.transitions()))
    n_cpus = utils.args.cpus if utils.args.cpus is not None else 1
    n_cpus = max(n_cpus, 2) # we need at least 2 processes or we will block on the last one that found a model
    t0 = timedelta(seconds=60) # the base unit for timeouts is 60 seconds (i.e., Luby sequence starts at 60 seconds)

    # the smallest set of ps for which the dual edge is known to be valid
    current_p = frozenset(range(n_ps))

    def hoare_queries_for_p(p: FrozenSet[int]) -> List[HoareQuery]:
        # return the queries that must all be unsat for a dual edge with the given p to be valid
        return [
            HoareQuery(
                p=p,
                q_pre=q_seed,
                q_post=tuple(q_seed[k] if k == i_q else frozenset() for k in range(mp.m)),
                cardinalities=(),
                i_transition=i_transition,
            )
            for i_transition in range(n_transitions)
            for i_q in range(mp.m)
        ]

    known_unsats = hoare_queries_for_p(current_p) # these are known to be unsat since we assume the given dual edge is valid
    def known_to_be_unsat(hq: HoareQuery) -> bool:
        return any(len(x) == 0 for x in hq.q_pre) or any(
            hq <= unsat_hq
            for unsat_hq in known_unsats
        )
    known_sats: List[HoareQuery] = []
    def known_to_be_sat(hq: HoareQuery) -> bool:
        return any(
            hq >= sat_hq
            for sat_hq in known_sats
        )
    def known_to_be_valid(p: FrozenSet[int]) -> bool:
        return all(known_to_be_unsat(hq) for hq in hoare_queries_for_p(p))
    def known_to_be_invalid(p: FrozenSet[int]) -> bool:
        return any(known_to_be_sat(hq) for hq in hoare_queries_for_p(p))

    assert known_to_be_valid(current_p)

    active_queries: List[HoareQuery] = list(chain(*(
        hoare_queries_for_p(current_p - {i})
        for i in sorted(current_p, reverse=True) # TODO: maybe random order?
    )))

    print(f'[{datetime.now()}] check_dual_edge_optimize_minimize_ps: initially with {len(active_queries)} active queries')

    running: List[RunningProcess] = [] # list of currently running processes

    # map (hq, use_cvc4) to number of attempts spent on it (note that attempt i takes Luby[i] time)
    # nothing is ever removed from tasks, and active_queries is used to maintain the active ones
    tasks: Dict[Tuple[HoareQuery, bool], int] = defaultdict(int)

    try:
        while True:
            # see if we got new results
            worklist = list(running)
            any_news = False
            while len(worklist) > 0:
                rp = worklist[0]
                try:
                    hq, valid, cti = rp.q1.get_nowait()
                    rp.q1.task_done()
                except queue.Empty:
                    worklist = worklist[1:]
                    continue
                any_news = True
                assert cti is None
                if valid:
                    # got new unsat result
                    # this may trigger changing the current_p, but we'll check that later since it requires more than one result
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_minimize_ps: got an UNSAT result from PID={rp.process.pid} for hq={hq}, use_cvc4={rp.use_cvc4}')
                    known_unsats.append(hq)
                else:
                    # got new sat result
                    # this makes some other queries unneeded, but we'll filter them later
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_minimize_ps: got a SAT result from PID={rp.process.pid} for hq={hq}, use_cvc4={rp.use_cvc4}')
                    known_sats.append(hq)

            if any_news:
                # check if we can lower the current_p
                for i in sorted(current_p, reverse=True): # TODO: maybe random order?
                    if known_to_be_valid(current_p - {i}):
                        print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_minimize_ps: removing {i}')
                        current_p -= {i}
                        active_queries = list(chain(*(
                            hoare_queries_for_p(current_p - {i})
                            for i in sorted(current_p, reverse=True) # TODO: maybe random order?
                        )))
                        break
                # filter using known facts and possibly return
                active_queries = [hq for hq in active_queries if not (
                    known_to_be_unsat(hq) or
                    known_to_be_sat(hq) or
                    known_to_be_invalid(hq.p)
                )]
                if len(active_queries) == 0:
                    # we are done
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_minimize_ps: no more active queries, returning optimial p ({len(current_p)} / {n_ps}): {sorted(current_p)}')
                    print(f'[{datetime.now()}] check_dual_edge_optimize_minimize_ps: done')
                    return current_p
                else:
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_minimize_ps: {len(active_queries)} more active queries, carrying on')
                    # for hq in active_queries:
                    #     print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_minimize_ps:     {hq}')
                    # print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_minimize_ps: carrying on')

            # kill processes that timed out or whose query is no longer active
            now = datetime.now()
            still_running = []
            for rp in running:
                if not rp.process.is_alive():
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_minimize_ps: process with PID={rp.process.pid} terminated')
                    rp.terminate()
                    assert rp.process.exitcode == 0, rp.process.exitcode
                elif all(rp.hq.replace_transition(i_transition) not in active_queries for i_transition in range(n_transitions)): # rp will also try other transitions
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_minimize_ps: terminating process with PID={rp.process.pid}, hq={rp.hq}, use_cvc4={rp.use_cvc4} due to another result')
                    rp.terminate()
                elif now > rp.deadline:
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_minimize_ps: terminating process with PID={rp.process.pid}, hq={rp.hq}, use_cvc4={rp.use_cvc4} due to timeout')
                    rp.terminate()
                else:
                    still_running.append(rp)
            running = still_running

            # start new processes
            active_tasks = list(product(
                active_queries, # hq
                [False, True], # use_cvc4
            ))
            while len(running) < n_cpus:
                task_to_run = min(active_tasks, key=tasks.__getitem__)
                hq, use_cvc4 = task_to_run
                timeout = t0 * luby(tasks[task_to_run])
                tasks[task_to_run] += 1
                q1 = CheckDualEdgeOptimizeJoinableQueue()
                q2 = CheckDualEdgeOptimizeQueue()
                args = (
                    ps,
                    top_clauses,
                    hq,
                    False, # produce_cti
                    False, # optimize
                    False, # whole_clauses
                    use_cvc4,
                    not use_cvc4 and tasks[task_to_run] == n_cpus + 1, # on the (n_cpu + 1)'th attempt, save to smt2 for later analysis
                    q1,
                    q2,
                )
                # assert_valid_hq(*args[:3])
                if TYPE_CHECKING: # trick to get typechecking for check_dual_edge_optimize_multiprocessing_helper
                    check_dual_edge_optimize_multiprocessing_helper(*args)
                process = multiprocessing.Process(
                    target=check_dual_edge_optimize_multiprocessing_helper,
                    args=args,
                )
                deadline = datetime.now() +  timeout
                print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_minimize_ps: starting new process for hq={hq}, use_cvc4={use_cvc4} with a timeout of {timeout.total_seconds()} seconds')
                rp = RunningProcess(
                    process,
                    q1,
                    q2,
                    deadline,
                    hq,
                    use_cvc4,
                )
                process.start()
                running.append(rp)

            # wait until we have new results, or until the next deadline expires
            earliest_deadline = min(
                (rp.deadline for rp in running),
                default=None,
            )
            seconds = (0.1 if earliest_deadline is None else
                       (earliest_deadline - datetime.now()).total_seconds())
            seconds = max(0.1, seconds)
            print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_minimize_ps: waiting for news with a timeout of {seconds} seconds')
            multiprocessing.connection.wait(
                [rp.q1._reader for rp in running], # type: ignore
                timeout=seconds,
            )
        assert False
    finally:
        # terminate all running processeses
        for rp in running:
            print(f'[{datetime.now()}] [PID={os.getpid()}] check_dual_edge_optimize_minimize_ps: terminating process with PID={rp.process.pid}')
            rp.terminate()
        assert len(multiprocessing.active_children()) == 0

def check_dual_edge_optimize(
        ps: Tuple[Expr,...],
        top_clauses: Tuple[Expr, ...],
        q_seed: Tuple[FrozenSet[int], ...],
        whole_clauses: bool = False, # if True, only try the empty clause or the entire top_clause (used in find_dual_backward_transition)
) -> Tuple[Optional[Tuple[PDState, PDState]], Optional[Tuple[Expr,...]]]:
    '''
    this checks if ps /\ qs |= wp(ps -> qs)
    qs are given by top_clauses and q_seed
    if there's a cti, we optimize it
    if there's an induction edge, we find a minimal subset of ps required
    for now there is no caching here
    '''
    prog = syntax.the_program
    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # must be in CNF for use in eval_in_state
    print(f'[{datetime.now()}] check_dual_edge_optimize: starting')
    mp = MultiSubclausesMapICE(top_clauses, [], []) # only used to get clauses from seeds
    assert len(q_seed) == mp.m
    assert all(all(i < mp.n[k] for i in q_seed[k]) for k in range(mp.m))
    qs = tuple(mp.to_clause(k, q_seed[k]) for k in range(mp.m))
    print(f'[{datetime.now()}] check_dual_edge_optimize: starting to check the following edge ({len(ps)}, {len(qs)}):')
    for p in ps:
        print(f'  {p}')
    print('  -->')
    for q in qs:
        print(f'  {q}')
    print(f'[{datetime.now()}] check_dual_edge_optimize_cache: starting')
    for prestate, poststate in _cache_transitions:
        if (all(eval_in_state(None, prestate,  p) for p in ps) and
            all(eval_in_state(None, prestate,  q) for q in qs) and
            all(eval_in_state(None, poststate, p) for p in ps) and not
            all(eval_in_state(None, poststate, q) for q in qs)
        ):
            print(f'[{datetime.now()}] check_dual_edge_optimize: found cached cti violating dual edge')
            print(f'[{datetime.now()}] check_dual_edge_optimize_cache: done')
            print(f'[{datetime.now()}] check_dual_edge_optimize: done')
            return ((prestate, poststate), None)
    print(f'[{datetime.now()}] check_dual_edge_optimize_cache: done')
    res = check_dual_edge_optimize_find_cti(ps, top_clauses, q_seed, whole_clauses)
    if res is not None:
        # res contains optimal cti
        prestate, poststate = res
        _cache_transitions.append((prestate, poststate))
        for state in (prestate, poststate):
            if all(eval_in_state(None, state, p) for p in inits):
                _cache_initial.append(state)
        print(f'[{datetime.now()}] check_dual_edge_optimize: found new cti violating dual edge')
        print(f'[{datetime.now()}] check_dual_edge_optimize: done')
        return ((prestate, poststate), None)
    else:
        # the dual edge is valid, minimize ps
        ps_i = check_dual_edge_optimize_minimize_ps(ps, top_clauses, q_seed)
        if False:
            # TODO: remove once we trust check_dual_edge_optimize_minimize_ps
            def check_old(ps_seed: FrozenSet[int]) -> bool:
                return check_dual_edge_multiprocessing_seeds(
                    ps=tuple(ps[i] for i in sorted(ps_seed)),
                    qs=qs,
                    minimize=False,
                ) is None
            assert check_old(ps_i)
            assert all(not check_old(ps_i - {i}) for i in sorted(ps_i))
        _ps = tuple(ps[i] for i in sorted(ps_i))
        print(f'[{datetime.now()}] check_dual_edge_optimize: found new valid dual edge:')
        for p in _ps:
            print(f'  {p}')
        print('  -->')
        for q in qs:
            print(f'  {q}')
        print(f'[{datetime.now()}] check_dual_edge_optimize: done')
        return (None, _ps)


def check_k_state_implication(
        s: Solver,
        precondition: Union[Iterable[Expr], PDState],
        p: Expr,
        k: int,
        msg: str = 'transition',
) -> Optional[Tuple[PDState,...]]:
    # TODO: we should cache these

    if not isinstance(precondition, PDState):
        precondition = tuple(precondition)

    om = check_bmc(
        s,
        p,
        k,
        [precondition.as_onestate_formula(0)] if isinstance(precondition, PDState) else precondition,
    )
    if om is None:
        return None
    else:
        # ODED: not sure if this is correct (see previous version below)
        states = tuple(
            om._as_trace(tuple(reversed(range(i + 1))))
            for i in range(om.num_states)
        )
        print(f'Found new {k}-{msg} violating {p}:')
        print('-'*80 + '\n' + str(states[-1]) + '\n' + '-'*80)
        return states

        # # TODO(jrw): I disabled this while removing the z3 model from Trace. Once we refactor
        # # this file to use logic.State for its states, this will be easy to re-enable.
        # reveal_type(om)
        # assert False
        # z3m = om.z3model
        # assert z3m is not None
        # keys = list(om.keys)
        # states = tuple(
        #     Trace.from_z3(keys[i:], z3m)
        #     for i in reversed(range(len(keys)))
        # )
        # print(f'Found new {k}-{msg} violating {p}:')
        # print('-'*80 + '\n' + str(states[-1]) + '\n' + '-'*80)
        # return states


class MapSolver:
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
        res = self.solver.check()
        assert res in (z3.unsat, z3.sat)
        if res == z3.unsat:
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


def alpha_from_clause_marco(solver:Solver, states: Iterable[PDState] , top_clause:Expr) -> Sequence[Expr]:
    # TODO: why can't top_clause be quantifier free?
    assert isinstance(top_clause, QuantifierExpr)
    assert isinstance(top_clause.body, NaryExpr)
    assert top_clause.body.op == 'OR'
    #assert free_ids(top_clause.body) == set(v.name for v in top_clause.binder.vs)
    literals = tuple(top_clause.body.args) # TODO: cannot sort sorted(top_clause.body.args)
    variables = tuple(top_clause.binder.vs)
    assert len(set(literals)) == len(literals)
    n = len(literals)
    print(f'the powerset is of size {2**n}', end='...\n')

    def to_clause(s: Set[int]) -> Expr:
        lits = [literals[i] for i in s]
        vs = tuple(v for v in variables if v.name in set(n for lit in lits for n in free_ids(lit)))
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


def subclauses(top_clause: Expr) -> Iterable[Expr]:
    variables, literals = destruct_clause(top_clause)
    assert len(set(literals)) == len(literals)
    n = len(literals)
    print(f'subclauses: the powerset is of size {2**n}')
    assert n**2 < 10**6, f'{2**n}, really??'
    for lits in powerset(literals):
        free = set(chain(*(free_ids(lit) for lit in lits)))
        vs = tuple(v for v in variables if v.name in free)
        yield Forall(vs, Or(*lits)) if len(vs) > 0 else Or(*lits)


def alpha_from_clause(solver:Solver, states: Iterable[PDState] , top_clause:Expr) -> Sequence[Expr]:
    assert isinstance(top_clause, QuantifierExpr)
    assert isinstance(top_clause.body, NaryExpr)
    assert top_clause.body.op == 'OR'
    #assert free_ids(top_clause.body) == set(v.name for v in top_clause.binder.vs)
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
        vs = tuple(v for v in top_clause.binder.vs
                   if v.name in set(n for lit in lits for n in free_ids(lit)))
        if len(vs) > 0:
            clause : Expr = Forall(vs, Or(*lits))
        else:
            clause = Or(*lits)
        if all(eval_in_state(solver, m, clause) for m in states):
            result.append(clause)
            implied.add(frozenset(lits))
    return result
alpha_from_clause = alpha_from_clause_marco


def alpha_from_predicates(s:Solver, states: Iterable[PDState] , predicates: Iterable[Expr]) -> Sequence[Expr]:
    return tuple(p for p in predicates if all(eval_in_state(s, m, p) for m in states))


# cache and helpers for multiprocessing for map_clause_state_interaction
_cache_map_clause_state_interaction: Dict[Tuple[Tuple[SortedVar,...], Tuple[Expr,...], Union[PDState, Expr]] ,Tuple[List[FrozenSet[int]], List[FrozenSet[int]]]] = dict()
# TODO: --cache-only checks for this cache (nothign right now)
def _map_clause_state_interaction_helper(vls: Tuple[Tuple[SortedVar,...], Tuple[Expr,...], Union[PDState, Expr]]) -> Tuple[List[FrozenSet[int]], List[FrozenSet[int]]]:
    if isinstance(vls[2], PDState):
        all_mss = map_clause_state_interaction_z3(vls[0], vls[1], vls[2].as_state(0))
        if False: # TODO: run at some point to verify
            all_mss2 = map_clause_state_interaction_instantiate(vls[0], vls[1], vls[2])
            #_, all_mss2 = map_clause_state_interaction(*vls)
            assert len(all_mss) == len(set(all_mss))
            assert len(all_mss2) == len(set(all_mss2))
            assert set(all_mss) == set(all_mss2), (sorted(all_mss), sorted(all_mss2))
        return [], all_mss
    else:
        return map_clause_state_interaction(*vls)
def multiprocessing_map_clause_state_interaction(work: List[Tuple[
        Tuple[SortedVar,...],
        Tuple[Expr,...],
        Union[PDState, Expr],
]]) -> List[Tuple[List[FrozenSet[int]], List[FrozenSet[int]]]]:
    real_work = [k for k in work if k not in _cache_map_clause_state_interaction]
    if False:
        # for debugging, compare results from cache to map_clause_state_interaction_instantiate
        for k in work:
            if k in _cache_map_clause_state_interaction and isinstance(k[2], PDState):
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
        results: List[Tuple[List[FrozenSet[int]], List[FrozenSet[int]]]] = []
        if n > 1:
            with multiprocessing.Pool(n) as pool:
               results = pool.map_async( # type: ignore # seems to be an issue with typeshed having wrong type for map_async, should
                   _map_clause_state_interaction_helper,
                   real_work,
               ).get(9999999) # see: https://stackoverflow.com/a/1408476
        else:
            results = list(map(_map_clause_state_interaction_helper, real_work))
        for k, v in zip(real_work, results):
            _cache_map_clause_state_interaction[k] = v
    return [_cache_map_clause_state_interaction[k] for k in work]


# cache and helper for multiprocessing for map_clause_state_size_interaction
_cache_clause_state_mss: Dict[Tuple[
    Tuple[SortedVar,...],
    Tuple[Expr,...],
    PDState,
], List[FrozenSet[int]]] = defaultdict(list) # maps to known MSSs
def _map_clause_state_size_interaction_helper(workitem: Tuple[
        Tuple[SortedVar,...], # variables
        Tuple[Expr,...], # literals
        PDState, # state
        int, # size
        List[FrozenSet[int]], # known MSSs of given state (will end up in all_mss)
        List[FrozenSet[int]], # MSSs to block (won't end up in all_mss)
        Optional[float], # timeout
]) -> Tuple[Optional[List[FrozenSet[int]]], List[FrozenSet[int]]]: # all_mss, new_mss
    variables, literals, state, size, known_mss, block_mss, timeout = workitem
    all_mss, new_mss = map_clause_state_size_interaction(variables, literals, state.as_state(0), size, known_mss, block_mss, timeout)
    return all_mss, new_mss
def multiprocessing_map_clause_state_size_interaction(work: List[Tuple[
        Tuple[SortedVar,...], # variables
        Tuple[Expr,...], # literals
        PDState, # state
        int, # size
        List[FrozenSet[int]], # block_mss
        Optional[float], # timeout
]]) -> List[Optional[List[FrozenSet[int]]]]:
    if len(work) == 0:
        return []
    if utils.args.cpus is None:
        n = 1
    else:
        n = min(utils.args.cpus, len(work))
    workitems = [
        (variables, literals, state, size, _cache_clause_state_mss[variables, literals, state], block_mss, timeout)
        for variables, literals, state, size, block_mss, timeout in work
    ]
    if n > 1:
        with multiprocessing.Pool(n) as pool:
           results = pool.map_async( # type: ignore # seems to be an issue with typeshed having wrong type for map_async, should
               _map_clause_state_size_interaction_helper,
               workitems
           ).get(9999999) # see: https://stackoverflow.com/a/1408476
    else:
        results = list(map(_map_clause_state_size_interaction_helper, workitems))
    for w, v in zip(work, results):
        _cache_clause_state_mss[w[:3]].extend(v[1])
    return [v[0] for v in results]

def map_clause_state_interaction(variables: Tuple[SortedVar,...],
                                 literals: Tuple[Expr,...],
                                 state_or_predicate: Union[PDState, Expr],
) -> Tuple[List[FrozenSet[int]], List[FrozenSet[int]]]:
    print(f' (PID={os.getpid()}) ', end='')
    cache = _cache_map_clause_state_interaction
    k = (variables, literals, state_or_predicate)
    if k in cache:
        print('found in cache!')
        return cache[k]

    def to_clause(s: Iterable[int]) -> Expr:
        lits = [literals[i] for i in sorted(s)]
        free = set(chain(*(free_ids(lit) for lit in lits)))
        vs = tuple(v for v in variables if v.name in free)
        return Forall(vs, Or(*lits)) if len(vs) > 0 else Or(*lits)

    n = len(literals)
    all_n = frozenset(range(n))
    solver = Solver()
    t = solver.get_translator(1)
    solver.add(t.translate_expr(
        state_or_predicate.as_onestate_formula(0) if isinstance(state_or_predicate, PDState) else
        state_or_predicate
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
    if isinstance(state_or_predicate, PDState) and False:  # not really needed if we have all the mss, TODO: should examine why so many mus and not so many mss, could be a bug
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
        state: PDState,
) -> List[FrozenSet[int]]:
    '''Return a list of maximal subclauses of the given clause (indices to
    literals) that are violated by the given state (equivalent to
    all_mss computed by map_clause_state_interaction), using explicit
    iteration over all quantifier instantiations.
    '''
    def ev(values: Sequence[str], lit: Expr) -> bool:
        # TODO: rewrite this with James, this is a hacky partial implementation of first-order logic semantics for class Trace (written on a plane from Phoenix to SF)
        assert len(variables) == len(values)
        consts_and_vars: Dict[str, str] = dict(chain(
            ((var.name, val) for var, val in zip(variables, values)),
            ((d.name, val) for d, val in state.as_state(0).const_interps.items())
        ))
        functions: Dict[str, Dict[Tuple[str,...], str]] = dict(
            (d.name, v) for d, v in state.as_state(0).func_interps.items()
        )
        relations: Dict[str, Dict[Tuple[str,...], bool]] = dict(
            (d.name, v) for d, v in state.as_state(0).rel_interps.items()
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
    print(f'[{datetime.now()}] map_clause_state_interaction_instantiate: PID={os.getpid()}, iterating over {n} instantiations... ')
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
    print(f'[{datetime.now()}] map_clause_state_interaction_instantiate: PID={os.getpid()}, iterated over {n} instantiations, found {len(result)} MSSs')
    return result


def map_clause_state_interaction_z3(
        variables: Tuple[SortedVar,...],
        literals: Tuple[Expr,...],
        state: State,
) -> List[FrozenSet[int]]:
    '''Return a list of maximal subclauses of the given clause (indices to
    literals) that are violated by the given state (equivalent to
    all_mss computed by map_clause_state_interaction), using an
    encoding into z3 using quantification over finite types to
    evaluate subclauses on the state.
    '''
    #
    import z3

    var_names = tuple(v.name for v in variables)
    sort_names = []
    for v in variables:
        assert isinstance(v.sort, UninterpretedSort)
        sort_names.append(v.sort.name)
    lit_vs = [z3.Bool(f'lit_{i}') for i in range(len(literals))]
    solver = z3.Solver()
    seen: Set[str] = set()  # used to assert we don't have name collisions
    size_vs = [z3.Bool(f'size_{i}') for i in range(len(literals))]

    for i, size_v in enumerate(size_vs):
        solver.add(z3.Implies(size_v, z3.AtMost(*lit_vs, i)))

    # encode state and force it to evaluate to false on the subclause encoded by lit_vs

    def p(st: str, must_be_new: bool = True) -> str:
        st = 'state_' + st
        assert (not must_be_new) or st not in seen, (st, seen)
        seen.add(st)
        return st

    assertions: List[z3.ExprRef] = []  # will be added to the solver

    # create z3 symbols for all relations, functions, and constants, and assert their meaning

    # create universe unary relations
    scope = max(len(elems) for elems in state.univs.values())
    V = z3.Datatype(p('elements'))
    def e(i: int) -> str:
        return f'e{i}'
    for i in range(scope):
        V.declare(e(i))
    V = V.create()
    def is_e(i: int) -> z3.FuncDeclRef:
        return getattr(V, 'is_' + e(i))
    def ee(i: int) -> z3.ExprRef:
        return getattr(V, e(i))
    universes = {s.name: z3.Function(p(s.name), V, z3.BoolSort()) for s in state.univs}
    elem_to_z3: Dict[str, z3.ExprRef] = {}
    for s, elems in state.univs.items():
        assertions.extend(universes[s.name](ee(i)) for i in range(len(elems)))
        assertions.extend(z3.Not(universes[s.name](ee(i))) for i in range(len(elems), scope))
        for i, elem in enumerate(elems):
            assert elem not in elem_to_z3
            elem_to_z3[elem] = ee(i)

    # create relations
    def lit(e: z3.ExprRef, polarity: bool) -> z3.ExprRef:
        return e if polarity else z3.Not(e)
    relations: Dict[str, Union[z3.ExprRef, z3.FuncDeclRef]] = {
        r.name:
        z3.Function(p(r.name), *repeat(V, len(r.arity)), z3.BoolSort()) if len(r.arity) > 0 else
        z3.Bool(p(r.name))
        for r in state.rel_interps
    }
    for r, ri in state.rel_interps.items():
        if len(r.arity) == 0:
            assert len(ri) == 1 and () in ri, (r, ri)
            a = relations[r.name]
            assert isinstance(a, z3.ExprRef)
            assertions.append(lit(a, ri[()]))
        else:
            for tup, polarity in ri.items():
                a = relations[r.name]
                assert isinstance(a, z3.FuncDeclRef)
                args = [elem_to_z3[x] for x in tup]
                assertions.append(lit(a(*args), polarity))

    # create functions
    assert all(len(f.arity) > 0 for f in state.func_interps)
    functions: Dict[str, z3.FuncDeclRef] = {
        f.name:
        z3.Function(p(f.name), *repeat(V, len(f.arity)), V)
        for f in state.func_interps
    }
    for f, fi in state.func_interps.items():
        for tup, img in fi.items():
            args = [elem_to_z3[x] for x in tup]
            assertions.append(functions[f.name](*args) == elem_to_z3[img])

    # create constants
    constants: Dict[str, z3.ExprRef] = {
        c.name: z3.Const(p(c.name), V)
        for c in state.const_interps
    }
    for c, ci in state.const_interps.items():
        assertions.append(constants[c.name] == elem_to_z3[ci])

    # now force state to evaluate to false on the subclause
    z3_vs = [z3.Const(p(f'V{i}'), V) for i in range(len(variables))]
    def to_z3(e: Expr) -> z3.ExprRef:
        if isinstance(e, Id):
            if e.name in var_names:
                return z3_vs[var_names.index(e.name)]
            elif e.name in constants:
                return constants[e.name]
            elif e.name in relations and isinstance(r := relations[e.name], z3.ExprRef):
                return r
            else:
                assert False, e
        elif isinstance(e, AppExpr) and e.callee in functions:
            return functions[e.callee](*(map(to_z3, e.args)))
        elif (isinstance(e, AppExpr) and e.callee in relations and
              isinstance(r := relations[e.callee], z3.FuncDeclRef)):
            return r(*(map(to_z3, e.args)))
        elif isinstance(e, UnaryExpr) and e.op == 'NOT':
            return z3.Not(to_z3(e.arg))
        elif isinstance(e, BinaryExpr) and e.op == 'EQUAL':
            return to_z3(e.arg1) == to_z3(e.arg2)
        elif isinstance(e, BinaryExpr) and e.op == 'NOTEQ':
            return to_z3(e.arg1) != to_z3(e.arg2)
        else:
            assert False, e
    value = z3.Implies(
        z3.And(*(
            universes[s](v)
            for v, s in zip(z3_vs, sort_names)
        )),
        z3.Or(*(
            z3.And(lit_v, to_z3(lit))
            for lit_v, lit in zip(lit_vs, literals)
        ))
    )
    if len(z3_vs) > 0:
        value = z3.ForAll(z3_vs, value)
    assertions.append(z3.Not(value))
    # now collect all maximal subclauses by finding all maximal satisfying assignments to lit_vs
    print(f'[{datetime.now()}] map_clause_state_interaction_z3: PID={os.getpid()}, iterating over ? instantiations... ')
    result: List[FrozenSet[int]] = []
    for a in assertions:
        solver.add(a)
    if True:
        while (z3_res := solver.check()) == z3.sat:
            z3m = solver.model()
            forced_to_true = set(
                i for i, v in enumerate(lit_vs)
                if not z3.is_false(z3m[v])
            )
            assert (res := solver.check(*(assumptions := [lit_vs[j] for j in sorted(forced_to_true)]))) == z3.sat, (res, str(assumptions), solver.to_smt2())
            for i in range(len(literals)):
                if i not in forced_to_true:
                    res = solver.check(*(lit_vs[j] for j in sorted(forced_to_true | {i})))
                    assert res in (z3.unsat, z3.sat), (res, solver.to_smt2())
                    if res == z3.sat:
                        forced_to_true.add(i)
            assert (res := solver.check(*(assumptions := [lit_vs[j] for j in sorted(forced_to_true)]))) == z3.sat, (res, str(assumptions), solver.to_smt2())
            # print(f'[{datetime.now()}] map_clause_state_interaction_z3: PID={os.getpid()}, found {len(result)+1:8}-th MSS ({len(forced_to_true):4}): {sorted(forced_to_true)}')
            if len(result) % 100 == 0:
                print(f'[{datetime.now()}] map_clause_state_interaction_z3: PID={os.getpid()}, found {len(result)+1:8}-th MSS')
            result.append(frozenset(forced_to_true))
            # block down
            solver.add(z3.Or(*(lit_vs[i] for i in range(len(literals)) if i not in forced_to_true)))
        assert z3_res == z3.unsat, (z3_res, solver.to_smt2())
    else:
        # version that explores by size
        for size_v in size_vs:
            print(f'[{datetime.now()}] map_clause_state_interaction_z3: PID={os.getpid()}, covering {size_v}...')
            while (z3_res := solver.check(size_v)) == z3.sat:
                z3m = solver.model()
                forced_to_true = set(
                    i for i, v in enumerate(lit_vs)
                    if not z3.is_false(z3m[v])
                )
                assert (res := solver.check(*(assumptions := [lit_vs[j] for j in sorted(forced_to_true)]))) == z3.sat, (res, str(assumptions), solver.to_smt2())
                for i in range(len(literals)):
                    if i not in forced_to_true:
                        res = solver.check(*(lit_vs[j] for j in sorted(forced_to_true | {i})))
                        assert res in (z3.unsat, z3.sat), (res, solver.to_smt2())
                        if res == z3.sat:
                            forced_to_true.add(i)
                assert (res := solver.check(*(assumptions := [lit_vs[j] for j in sorted(forced_to_true)]))) == z3.sat, (res, str(assumptions), solver.to_smt2())
                # print(f'[{datetime.now()}] map_clause_state_interaction_z3: PID={os.getpid()}, found {len(result)+1:8}-th MSS ({len(forced_to_true):4}): {sorted(forced_to_true)}')
                if len(result) % 100 == 0:
                    print(f'[{datetime.now()}] map_clause_state_interaction_z3: PID={os.getpid()}, found {len(result)+1:8}-th MSS')
                result.append(frozenset(forced_to_true))
                # block down
                solver.add(z3.Or(*(lit_vs[i] for i in range(len(literals)) if i not in forced_to_true)))
            assert z3_res == z3.unsat, (z3_res, solver.to_smt2())
            print(f'[{datetime.now()}] map_clause_state_interaction_z3: PID={os.getpid()}, covered {size_v} with a total of {len(result)} MSSs')
    print(f'[{datetime.now()}] map_clause_state_interaction_z3: PID={os.getpid()}, iterated over ? instantiations, found {len(result)} MSSs')
    return result


def map_clause_state_size_interaction(
        variables: Tuple[SortedVar,...],
        literals: Tuple[Expr,...],
        state: State,
        size: int,
        known_mss: List[FrozenSet[int]],
        block_mss: List[FrozenSet[int]],
        timeout: Optional[float],
) -> Tuple[Optional[List[FrozenSet[int]]], List[FrozenSet[int]]]: # all_mss, new_mss
    '''Return a list of maximal subclauses of the given clause (indices to
    literals) that are violated by the given state that cover all
    subclauses up to given size.

    On timeout, return (None, new_mss), with the new MSSs found
    '''
    #
    t_start = datetime.now()
    import z3
    if timeout is None:
        timeout =  float('inf')
    var_names = tuple(v.name for v in variables)
    sort_names = []
    for v in variables:
        assert isinstance(v.sort, UninterpretedSort)
        sort_names.append(v.sort.name)
    lit_vs = [z3.Bool(f'lit_{i}') for i in range(len(literals))]
    solver = z3.Solver()
    seen: Set[str] = set()  # used to assert we don't have name collisions
    size_v = z3.Bool(f'size_v')

    # constraint size
    solver.add(z3.Implies(size_v, z3.AtMost(*lit_vs, size)))

    # block MSSs in block_mss
    for mss in block_mss:
        solver.add(z3.Or(*(lit_vs[i] for i in range(len(literals)) if i not in mss)))

    # encode state and force it to evaluate to false on the subclause encoded by lit_vs

    def p(st: str, must_be_new: bool = True) -> str:
        st = 'state_' + st
        assert (not must_be_new) or st not in seen, (st, seen)
        seen.add(st)
        return st

    assertions: List[z3.ExprRef] = []  # will be added to the solver

    # create z3 symbols for all relations, functions, and constants, and assert their meaning

    # create universe unary relations
    scope = max(len(elems) for elems in state.univs.values())
    V = z3.Datatype(p('elements'))
    def e(i: int) -> str:
        return f'e{i}'
    for i in range(scope):
        V.declare(e(i))
    V = V.create()
    def is_e(i: int) -> z3.FuncDeclRef:
        return getattr(V, 'is_' + e(i))
    def ee(i: int) -> z3.ExprRef:
        return getattr(V, e(i))
    universes = {s.name: z3.Function(p(s.name), V, z3.BoolSort()) for s in state.univs}
    elem_to_z3: Dict[str, z3.ExprRef] = {}
    for s, elems in state.univs.items():
        assertions.extend(universes[s.name](ee(i)) for i in range(len(elems)))
        assertions.extend(z3.Not(universes[s.name](ee(i))) for i in range(len(elems), scope))
        for i, elem in enumerate(elems):
            assert elem not in elem_to_z3
            elem_to_z3[elem] = ee(i)

    # create relations
    def lit(e: z3.ExprRef, polarity: bool) -> z3.ExprRef:
        return e if polarity else z3.Not(e)
    relations: Dict[str, Union[z3.ExprRef, z3.FuncDeclRef]] = {
        r.name:
        z3.Function(p(r.name), *repeat(V, len(r.arity)), z3.BoolSort()) if len(r.arity) > 0 else
        z3.Bool(p(r.name))
        for r in state.rel_interps
    }
    for r, ri in state.rel_interps.items():
        if len(r.arity) == 0:
            assert len(ri) == 1 and () in ri, (r, ri)
            a = relations[r.name]
            assert isinstance(a, z3.ExprRef)
            assertions.append(lit(a, ri[()]))
        else:
            for tup, polarity in ri.items():
                a = relations[r.name]
                assert isinstance(a, z3.FuncDeclRef)
                args = [elem_to_z3[x] for x in tup]
                assertions.append(lit(a(*args), polarity))

    # create functions
    assert all(len(f.arity) > 0 for f in state.func_interps)
    functions: Dict[str, z3.FuncDeclRef] = {
        f.name:
        z3.Function(p(f.name), *repeat(V, len(f.arity)), V)
        for f in state.func_interps
    }
    for f, fi in state.func_interps.items():
        for tup, img in fi.items():
            args = [elem_to_z3[x] for x in tup]
            assertions.append(functions[f.name](*args) == elem_to_z3[img])

    # create constants
    constants: Dict[str, z3.ExprRef] = {
        c.name: z3.Const(p(c.name), V)
        for c in state.const_interps
    }
    for c, ci in state.const_interps.items():
        assertions.append(constants[c.name] == elem_to_z3[ci])

    # now force state to evaluate to false on the subclause
    z3_vs = [z3.Const(p(f'V{i}'), V) for i in range(len(variables))]
    def to_z3(e: Expr) -> z3.ExprRef:
        if isinstance(e, Id):
            if e.name in var_names:
                return z3_vs[var_names.index(e.name)]
            elif e.name in constants:
                return constants[e.name]
            elif e.name in relations and isinstance(r := relations[e.name], z3.ExprRef):
                return r
            else:
                assert False, e
        elif isinstance(e, AppExpr) and e.callee in functions:
            return functions[e.callee](*(map(to_z3, e.args)))
        elif (isinstance(e, AppExpr) and e.callee in relations and
              isinstance(r := relations[e.callee], z3.FuncDeclRef)):
            return r(*(map(to_z3, e.args)))
        elif isinstance(e, UnaryExpr) and e.op == 'NOT':
            return z3.Not(to_z3(e.arg))
        elif isinstance(e, BinaryExpr) and e.op == 'EQUAL':
            return to_z3(e.arg1) == to_z3(e.arg2)
        elif isinstance(e, BinaryExpr) and e.op == 'NOTEQ':
            return to_z3(e.arg1) != to_z3(e.arg2)
        else:
            assert False, e
    value = z3.Implies(
        z3.And(*(
            universes[s](v)
            for v, s in zip(z3_vs, sort_names)
        )),
        z3.Or(*(
            z3.And(lit_v, to_z3(lit))
            for lit_v, lit in zip(lit_vs, literals)
        ))
    )
    if len(z3_vs) > 0:
        value = z3.ForAll(z3_vs, value)
    assertions.append(z3.Not(value))

    for a in assertions:
        solver.add(a)

    all_mss: List[FrozenSet[int]] = known_mss[:] # for now we use all known MSSs. later we can try to use unsat core to minimize the result
    new_mss: List[FrozenSet[int]] = []
    # block all known MSSs
    for mss in known_mss:
        solver.add(z3.Or(*(lit_vs[i] for i in range(len(literals)) if i not in mss)))
    # now collect more maximal subclauses violating state until size is covered
    print(f'[{datetime.now()}] map_clause_state_size_interaction: PID={os.getpid()}, covering size {size}...')
    while (not (timedout := (datetime.now() - t_start).total_seconds() >= timeout) and
           (z3_res := solver.check(size_v)) == z3.sat):
        z3m = solver.model()
        forced_to_true = set(
            i for i, v in enumerate(lit_vs)
            if not z3.is_false(z3m[v])
        )
        assert (res := solver.check(*(assumptions := [lit_vs[j] for j in sorted(forced_to_true)]))) == z3.sat, (res, str(assumptions), solver.to_smt2())
        for i in range(len(literals)):
            if i not in forced_to_true:
                res = solver.check(*(lit_vs[j] for j in sorted(forced_to_true | {i})))
                assert res in (z3.unsat, z3.sat), (res, solver.to_smt2())
                if res == z3.sat:
                    forced_to_true.add(i)
        assert (res := solver.check(*(assumptions := [lit_vs[j] for j in sorted(forced_to_true)]))) == z3.sat, (res, str(assumptions), solver.to_smt2())
        # print(f'[{datetime.now()}] map_clause_state_size_interaction: PID={os.getpid()}, found {len(result)+1:8}-th new MSS ({len(forced_to_true):4}): {sorted(forced_to_true)}')
        mss = frozenset(forced_to_true)
        all_mss.append(mss)
        new_mss.append(mss)
        if (len(new_mss) - 1) % 100 == 0:
            print(f'[{datetime.now()}] map_clause_state_size_interaction: PID={os.getpid()}, found {len(new_mss):8}-th new MSS ({len(all_mss)} total MSSs)')
        # block down
        solver.add(z3.Or(*(lit_vs[i] for i in range(len(literals)) if i not in forced_to_true)))
    if timedout:
        print(f'[{datetime.now()}] map_clause_state_size_interaction: PID={os.getpid()}, timed out while covering {size}, found {len(new_mss)} new MSSs')
        return None, new_mss
    else:
        assert z3_res == z3.unsat, (z3_res, solver.to_smt2())
        print(f'[{datetime.now()}] map_clause_state_size_interaction: PID={os.getpid()}, covered {size} in {(datetime.now() - t_start).total_seconds()} seconds, found {len(new_mss)} new MSSs, total of {len(all_mss)} MSSs')
        return all_mss, new_mss


class SubclausesMapTurbo:
    '''
    Class used to store a map of subclauses of a certain clause, and
    obtain subclauses that are positive and negative on some given
    states.
    '''
    def __init__(self,
                 top_clause: Expr,
                 states: List[PDState],  # assumed to only grow
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
        print(f'[{datetime.now()}] Mapping out subclauses-state interaction with {len(new)} new states for {self.to_clause(self.all_n)}')
        total_mus = 0
        total_mss = 0
        results = multiprocessing_map_clause_state_interaction([
            (self.variables, self.literals, self.states[i])
            for i in new
        ])
        for i in new:
            # print(f'[{datetime.now()}] Mapping out subclauses-state interaction with states[{i}]... ', end='')
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
        print(f'[{datetime.now()}] Mapping out subclauses-predicate interaction with {len(new)} new predicates for {self.to_clause(self.all_n)}')
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
                self.solver.add_soft(c)  # type: ignore
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
        free = set(chain(*(free_ids(lit) for lit in lits)))
        vs = tuple(v for v in self.variables if v.name in free)
        return Forall(vs, Or(*lits)) if len(vs) > 0 else Or(*lits)


class MultiSubclausesMapICE:
    '''Class used to store a map of subclauses of several clauses, and
    obtain a conjunction of subclauses that satisfy positive,
    negative, and implication constraints on some given states.
    '''
    def __init__(self,
                 top_clauses: Sequence[Expr],
                 states: List[PDState],  # assumed to only grow
                 predicates: List[Expr],  # assumed to only grow
                 # optimize: bool = False, # see comment about soft_* in separate
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
        self.all_n = [frozenset(range(self.n[k])) for k in range(self.m)]  # used in complement fairly frequently
        self.optimize = False # optimize
        self.solver = z3.Optimize() if self.optimize else z3.Solver()  # type: ignore # TODO - fix typing
        self.lit_vs = [[z3.Bool(f'lit_{k}_{i}') for i in range(self.n[k])] for k in range(self.m)] # lit_vs[k][i] represents the i'th literal in the k'th clause
        self.var_vs = [[z3.Bool(f'var_{k}_{i}') for i in range(len(self.variables[k]))] for k in range(self.m)] # var_vs[k][i] represents the i'th variable in the k'th clause
        self.state_vs: List[List[z3.ExprRef]] = [[] for k in range(self.m)] # state_vs[k][i] represents the value of the k'th clause in self.states[i]
        self.predicate_vs: List[List[z3.ExprRef]] = [[] for k in range(self.m)] # predicate_vs[k][i] represents the implication of value of the k'th clause by self.predicates[i]
        self.states_mapped: Set[int] = set() # i for which states[i] has been mapped and self.state_vs[*][i] is constrained in the solver

        if utils.args.domain_independence:
            self._constrain_domain_independence()

        self._constrain_variables()

    def _constrain_variables(self) -> None:
        for k in range(self.m):
            d: Dict[str, int] = {
                v.name: i
                for i, v in enumerate(self.variables[k])
            }
            for i, l in enumerate(self.literals[k]):
                for name in sorted(free_ids(l)):
                    if name in d:
                        self.solver.add(z3.Implies(self.lit_vs[k][i], self.var_vs[k][d[name]]))

    def _constrain_domain_independence(self) -> None:
        '''for each equality literal between two vars, if the literal is used, then some "domain constraining" literal for each var must also be used.'''
        def destruct_variable_equality(lit: Expr) -> Optional[Tuple[str, str]]:
            if not isinstance(lit, BinaryExpr):
                return None
            if lit.op == 'NOTEQ':
                return None
            assert lit.op == 'EQUAL', lit.op
            left = lit.arg1
            right = lit.arg2
            def is_var(x: Id) -> bool:
                prog = syntax.the_program
                scope = prog.scope
                o = scope.get(x.name)
                assert o is None or isinstance(o, ConstantDecl)
                return o is None
            if (not isinstance(left, Id) or not is_var(left) or
               not isinstance(right, Id) or not is_var(right)):
                return None
            else:
                return left.name, right.name

        def domain_independent_literals_for_var(lits: Tuple[Expr, ...], v: str) -> Iterable[int]:
            for j, lit in enumerate(lits):
                if v in free_ids(lit) and destruct_variable_equality(lit) is None:
                    yield j

        for k in range(self.m):
            for i, l in enumerate(self.literals[k]):
                o = destruct_variable_equality(l)
                if o is not None:
                    for v in o:
                        self.solver.add(z3.Implies(self.lit_vs[k][i], z3.Or(*[self.lit_vs[k][j] for j in domain_independent_literals_for_var(self.literals[k], v)])))

    def _new_states(self, to_map: List[int]) -> None:
        if self.m == 0:
            return
        # first, just add new variables for all new states
        new = range(len(self.state_vs[0]), len(self.states))
        for k in range(self.m):
            self.state_vs[k].extend(z3.Bool(f's_{k}_{i}') for i in new)
        # now, actually map the states that are needed to map
        to_map = sorted(set(to_map) - self.states_mapped)
        if len(to_map) == 0:
            return
        self.states_mapped.update(to_map)
        for k in range(self.m):
            print(f'[{datetime.now()}] Mapping out subclauses-state interaction with {len(to_map)} new states for {self.to_clause(k, self.all_n[k])}')
            total_mus = 0
            total_mss = 0
            results = multiprocessing_map_clause_state_interaction([
                (self.variables[k], self.literals[k], self.states[i])
                for i in to_map
            ])
            for i in to_map:
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
            print(f'[{datetime.now()}] Done subclauses-states (total_cdnf={total_mus + total_mss}, total_mus={total_mus}, total_mss={total_mss})')

    def _new_predicates(self) -> None:
        if self.m == 0:
            return
        new = range(len(self.predicate_vs[0]), len(self.predicates))
        if len(new) == 0:
            return
        for k in range(self.m):
            self.predicate_vs[k].extend(z3.Bool(f'p_{k}_{i}') for i in new)
            print(f'[{datetime.now()}] Mapping out subclauses-predicate interaction with {len(new)} new predicates for {self.to_clause(k, self.all_n[k])}')
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
                self.solver.add(self.predicate_vs[k][i] == z3.And(*(
                    z3.Or(*(
                        self.lit_vs[k][j] for j in sorted(self.all_n[k] - v)
                    ))
                    for v in all_mss
                )))
                total_mus += len(all_mus)
                total_mss += len(all_mss)
            print(f'[{datetime.now()}] Done subclauses-predicates (total_cdnf={total_mus + total_mss}, total_mus={total_mus}, total_mss={total_mss})')

    def separate(self,
                 pos: Collection[int] = (),
                 neg: Collection[int] = (),
                 imp: Collection[Tuple[int, int]] = (),
                 pos_ps: Collection[int] = (), # each clause must be implied by these predicates (used to force initiation)
                 neg_ps: Collection[int] = (), # each clause must not be implied by these predicates
                 # the following were removed when we saw z3.Optimize is slow. maybe bring back later with local optimization:
                 # soft_pos: Collection[int] = (),
                 # soft_neg: Collection[int] = (),
                 # soft_imp: Collection[Tuple[int, int]] = (),
                 # soft_pos_ps: Collection[int] = (),
                 # soft_neg_ps: Collection[int] = (),
    ) -> Optional[List[FrozenSet[int]]]:
        '''
        find a conjunction of subclauses that respects given constraints, and optionally as many soft constraints as possible

        TODO: to we need an unsat core in case there is no subclause?

        NOTE: the result must contain a subclause of each top clause, i.e., true cannot be used instead of one of the top clauses
        '''
        soft_pos: Collection[int] = ()
        soft_neg: Collection[int] = ()
        soft_imp: Collection[Tuple[int, int]] = ()
        soft_pos_ps: Collection[int] = ()
        soft_neg_ps: Collection[int] = ()
        self._new_states(list(chain(
            pos,
            neg,
            chain(*imp),
            soft_pos,
            soft_neg,
            chain(*soft_imp),
        )))
        self._new_predicates()
        print(f'[{datetime.now()}] MultiSubclausesMapICE.separate: starting')
        assert all(0 <= i < len(self.states) for i in chain(pos, neg, soft_pos, soft_neg))
        assert all(0 <= i < len(self.predicates) for i in chain(pos_ps, neg_ps, soft_pos_ps, soft_neg_ps))
        sep = list(chain(
            (z3.And(*(self.state_vs[k][i] for k in range(self.m))) for i in sorted(pos)),
            (z3.Or(*(z3.Not(self.state_vs[k][i]) for k in range(self.m))) for i in sorted(neg)),
            (z3.Implies(
                z3.And(*(self.state_vs[k][i] for k in range(self.m))),
                z3.And(*(self.state_vs[k][j] for k in range(self.m))),
            ) for i, j in sorted(imp)),
            (z3.And(*(self.predicate_vs[k][i] for k in range(self.m))) for i in sorted(pos_ps)),
            (z3.And(*(z3.Not(self.predicate_vs[k][i]) for k in range(self.m))) for i in sorted(neg_ps)),
        ))
        soft = list(chain(
            (z3.And(*(self.state_vs[k][i] for k in range(self.m))) for i in sorted(soft_pos)),
            (z3.Or(*(z3.Not(self.state_vs[k][i]) for k in range(self.m))) for i in sorted(soft_neg)),
            (z3.Implies(
                z3.And(*(self.state_vs[k][i] for k in range(self.m))),
                z3.And(*(self.state_vs[k][j] for k in range(self.m))),
            ) for i, j in sorted(soft_imp)),
            (z3.And(*(self.predicate_vs[k][i] for k in range(self.m))) for i in sorted(soft_pos_ps)),
            (z3.And(*(z3.Not(self.predicate_vs[k][i]) for k in range(self.m))) for i in sorted(soft_neg_ps)),
            # also optimize for smaller clauses
            (z3.Not(v) for v in chain(*self.lit_vs)),
        ))
        self.solver.push()
        for c in sep:
            self.solver.add(c)
        if self.optimize:
            for c in soft:
                self.solver.add_soft(c)  # type: ignore
        print(f'[{datetime.now()}] Checking MultiSubclausesMapICE.solver... ')
        t_start = datetime.now()
        res = self.solver.check()
        t_end = datetime.now()
        print(f'[{datetime.now()}] Checking MultiSubclausesMapICE.solver... got {res}')
        assert res in (z3.unsat, z3.sat)
        if (t_end - t_start).total_seconds() > 3600:
            # TODO: Optimize does not have to_smt2, is sexpr the same?
            smt2 = self.solver.sexpr()  # type: ignore
            fn = f'{sha1(smt2.encode()).hexdigest()}.sexpr'
            print(f'[{datetime.now()}] MultiSubclausesMapICE.separate: that took very long, saving saving query to {fn} ({len(smt2)} bytes)')
            open(fn, 'w').write(smt2)
        if res == z3.unsat:
            self.solver.pop()
            print(f'[{datetime.now()}] MultiSubclausesMapICE.separate: done')
            return None
        # minimize the number of quantifiers used (this was written for z3.Solver, not z3.Optimize)
        for n in itertools.count():
            if utils.args.max_quantifiers is not None and n > utils.args.max_quantifiers:
                self.solver.pop()
                print(f'[{datetime.now()}] MultiSubclausesMapICE.separate: reached maximal number of quantifiers')
                print(f'[{datetime.now()}] MultiSubclausesMapICE.separate: done')
                return None
            self.solver.push()
            for k in range(self.m):
                self.solver.add(z3.AtMost(*self.var_vs[k], n))
            print(f'[{datetime.now()}] Checking MultiSubclausesMapICE.solver (optimizing quantifiers, n={n})... ')
            res = self.solver.check()
            print(f'[{datetime.now()}] Checking MultiSubclausesMapICE.solver (optimizing quantifiers, n={n})... got {res}')
            assert res in (z3.unsat, z3.sat)
            if res == z3.sat:
                model = self.solver.model()
                forced_to_false = [set(
                    i for i, v in enumerate(self.lit_vs[k])
                    if not z3.is_true(model[v])
                ) for k in range(self.m)]
                self.solver.pop()
                for k in range(self.m):
                    self.solver.add(z3.AtMost(*self.var_vs[k], n))
                break
            else:
                self.solver.pop()
        if not self.optimize:
            # minimize for strongest possible clause (and ignore other soft constraints)
            for k in range(self.m):
                for i in range(self.n[k]):
                    if i not in forced_to_false[k]:
                        ki = [(kk, ii) for kk in range(self.m) for ii in forced_to_false[kk]] + [(k, i)]
                        print(f'[{datetime.now()}] Checking MultiSubclausesMapICE.solver (optimizing literals)... ')
                        res = self.solver.check(*(z3.Not(self.lit_vs[kk][ii]) for kk, ii in sorted(ki)))
                        print(f'[{datetime.now()}] Checking MultiSubclausesMapICE.solver (optimizing literals)... got {res}')
                        assert res in (z3.unsat, z3.sat)
                        if res == z3.sat:
                            model = self.solver.model()
                            for kk in range(self.m):
                                for ii, v in enumerate(self.lit_vs[k]):
                                    if ii not in forced_to_false[kk] and not z3.is_true(model[v]):
                                        forced_to_false[kk].add(ii)
                            assert i in forced_to_false[k]
        ki = [(kk, ii) for kk in range(self.m) for ii in forced_to_false[kk]]
        assert self.solver.check(*(z3.Not(self.lit_vs[kk][ii]) for kk, ii in sorted(ki))) == z3.sat # TODO: remove assertion after we are confident about this code
        result = [frozenset(self.all_n[k] - forced_to_false[k]) for k in range(self.m)]
        self.solver.pop()
        print(f'[{datetime.now()}] MultiSubclausesMapICE.separate: done')
        return result

    def to_clause(self, k: int, s: Iterable[int]) -> Expr:
        s = sorted(s)
        assert 0 <= k < self.m, (k, s, self.m, self.n)
        assert all(0 <= i < self.n[k] for i in s), (k, s, self.m, self.n)
        lits = [self.literals[k][i] for i in s]
        free = set(chain(*(free_ids(lit) for lit in lits)))
        vs = tuple(v for v in self.variables[k] if v.name in free)
        return Forall(vs, Or(*lits)) if len(vs) > 0 else Or(*lits)


class MultiSubclausesMapBySizeSep:
    '''Class used to store a map of subclauses of several clauses, and
    obtain a conjunction of subclauses that satisfy positive,
    negative, and implication constraints on some given states. This
    class computes and maintains the mapping between subclauses and
    states by the size of subclauses, namely, number of literals,
    significantly speeding up the search for small subclauses.

    '''
    def __init__(self,
                 top_clauses: Sequence[Expr],
                 states: List[PDState],  # assumed to only grow
                 predicates: List[Expr],  # assumed to only grow
                 # optimize: bool = False, # see comment about soft_* in separate
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
        self.all_n = [frozenset(range(self.n[k])) for k in range(self.m)]  # used in complement fairly frequently
        self.solver = z3.Solver()
        self.lit_vs = [[z3.Bool(f'lit_{k}_{i}') for i in range(self.n[k])] for k in range(self.m)] # lit_vs[k][i] represents the i'th literal in the k'th clause
        self.var_vs = [[z3.Bool(f'var_{k}_{i}') for i in range(len(self.variables[k]))] for k in range(self.m)] # var_vs[k][i] represents the i'th variable in the k'th clause
        self.size_vs = [[z3.Bool(f'size_{k}_{i}') for i in range(self.n[k])] + [z3.BoolVal(True)] for k in range(self.m)] # size_vs[k][i] represents that the k'th clause has at most i literals (for 0 <= i <= n[k])
        self.predicate_vs: List[List[z3.ExprRef]] = [[] for k in range(self.m)] # predicate_vs[k][i] represents the implication of value of the k'th clause by self.predicates[i]
        self.state_size_mapped: Set[Tuple[int,int,int]] = set() # (k, i, n) in the set means for states[i] and clause k, subclauses up to size n have been found and mapped in the solver, i.e., z3.Implies(size_vs[k][n], state_vs[k][i] == ...)
        self._state_vs: Dict[Tuple[int, int], z3.ExprRef] = dict()
        self.permanent_pos: Set[int] = set() # indices into self.states for which we permanently force separators to be true
        self.blocked_mss: List[Set[FrozenSet[int]]] = [set() for k in range(self.m)]

        if utils.args.domain_independence:
            self._constrain_domain_independence()
        self._constrain_variables()
        self._constrain_size()

    def state_v(self, k: int, i: int) -> z3.ExprRef:
        '''state_v(k, i) represents the value of the k'th clause in self.states[i]'''
        if (k, i) not in self._state_vs:
            self._state_vs[k, i] = z3.Bool(f'state_{k}_{i}')
        return self._state_vs[k, i]

    def _constrain_size(self) -> None:
        for k in range(self.m):
            for i, size_v in enumerate(self.size_vs[k]):
                self.solver.add(z3.Implies(size_v, z3.AtMost(*self.lit_vs[k], i)))

    def _constrain_variables(self) -> None:
        for k in range(self.m):
            d: Dict[str, int] = {
                v.name: i
                for i, v in enumerate(self.variables[k])
            }
            for i, l in enumerate(self.literals[k]):
                for name in sorted(free_ids(l)):
                    if name in d:
                        self.solver.add(z3.Implies(self.lit_vs[k][i], self.var_vs[k][d[name]]))

    def _constrain_domain_independence(self) -> None:
        '''for each equality literal between two vars, if the literal is used, then some "domain constraining" literal for each var must also be used.'''
        def destruct_variable_equality(lit: Expr) -> Optional[Tuple[str, str]]:
            if not isinstance(lit, BinaryExpr):
                return None
            if lit.op == 'NOTEQ':
                return None
            assert lit.op == 'EQUAL', lit.op
            left = lit.arg1
            right = lit.arg2
            def is_var(x: Id) -> bool:
                prog = syntax.the_program
                scope = prog.scope
                o = scope.get(x.name)
                assert o is None or isinstance(o, ConstantDecl)
                return o is None
            if (not isinstance(left, Id) or not is_var(left) or
               not isinstance(right, Id) or not is_var(right)):
                return None
            else:
                return left.name, right.name

        def domain_independent_literals_for_var(lits: Tuple[Expr, ...], v: str) -> Iterable[int]:
            for j, lit in enumerate(lits):
                if v in free_ids(lit) and destruct_variable_equality(lit) is None:
                    yield j

        for k in range(self.m):
            for i, l in enumerate(self.literals[k]):
                o = destruct_variable_equality(l)
                if o is not None:
                    for v in o:
                        self.solver.add(z3.Implies(self.lit_vs[k][i], z3.Or(*[self.lit_vs[k][j] for j in domain_independent_literals_for_var(self.literals[k], v)])))

    def _new_states_size(self, size: Sequence[int], states_to_map: Iterable[int]) -> None:
        '''states_to_map is a list of indices into self.states, size is a self.m long
        list with the size of each clause.
        '''
        if self.m == 0:
            return
        assert len(size) == self.m
        # now, actually map the states that are needed to map
        to_map = sorted(set((k, i, size[k]) for k in range(self.m) for i in states_to_map) - self.state_size_mapped)
        if len(to_map) == 0:
            return
        self.state_size_mapped.update(to_map)
        print(f'[{datetime.now()}] _new_states_size: starting')
        print(f'[{datetime.now()}] Mapping out subclauses-state interaction with {len(to_map)} work items for size {size} for top_clauses: {[str(self.to_clause(k, self.all_n[k])) for k in range(self.m)]}')
        total_mss = 0
        results = multiprocessing_map_clause_state_size_interaction([(
            self.variables[k],
            self.literals[k],
            self.states[i],
            n,
            sorted(self.blocked_mss[k]),
            None,
        ) for k, i, n in to_map])
        for (k, i, n), all_mss in zip(to_map, results):
            # could also have used something more fine grained here,
            # with ==> unconditioned and only <== conditioned on
            # size_v. we can try this if solver.check starts to take
            # too long in separate.
            assert all_mss is not None, (k, i, n)
            self.solver.add(z3.Implies(self.size_vs[k][n], self.state_v(k, i) == z3.And(*(
                z3.Or(*(
                    self.lit_vs[k][j] for j in sorted(self.all_n[k] - v)
                ))
                for v in all_mss
            ))))
            total_mss += len(all_mss)
        print(f'[{datetime.now()}] Done subclauses-states (total_new_mss={total_mss})')
        print(f'[{datetime.now()}] _new_states_size: done')

    def _new_permanent_pos_size(self, size: Sequence[int], permanent_pos: Set[int]) -> None:
        '''states_to_map is a list of indices into self.states, size is a self.m long
        list with the size of each clause.
        '''
        if self.m == 0:
            return
        assert len(size) == self.m
        assert self.permanent_pos <= permanent_pos
        for i in sorted(permanent_pos - self.permanent_pos):
            for k in range(self.m):
                self.solver.add(self.state_v(k, i))
        self.permanent_pos |= permanent_pos
        # now, actually map the states that are needed to map
        print(f'[{datetime.now()}] _new_permanent_pos_size: starting')
        to_map = sorted(set((k, i, size[k]) for k in range(self.m) for i in self.permanent_pos) - self.state_size_mapped)
        timeout = 60.0
        while len(to_map) > 0:
            print(f'[{datetime.now()}] Mapping out subclauses-state interaction with {len(to_map)} work items for size {size} and timeout {timeout} for top_clauses: {[str(self.to_clause(k, self.all_n[k])) for k in range(self.m)]}')
            new_blocked_mss = 0
            results = multiprocessing_map_clause_state_size_interaction([(
                self.variables[k],
                self.literals[k],
                self.states[i],
                n,
                sorted(self.blocked_mss[k]),
                timeout
            ) for k, i, n in to_map])
            next_to_map: List[Tuple[int, int, int]] = []
            for (k, i, n), all_mss in zip(to_map, results):
                for mss in _cache_clause_state_mss[self.variables[k], self.literals[k], self.states[i]]:
                    if mss not in self.blocked_mss[k]:
                        self.solver.add(z3.Or(*(
                            self.lit_vs[k][j] for j in sorted(self.all_n[k] - mss)
                        )))
                        self.blocked_mss[k].add(mss)
                        new_blocked_mss += 1
                if all_mss is None:
                    # timed out, should revisit
                    next_to_map.append((k, i, n))
                else:
                    # mark as mapped
                    self.state_size_mapped.add((k, i, n))
            print(f'[{datetime.now()}] Done subclauses-states (new_blocked_mss={new_blocked_mss})')
            if new_blocked_mss == 0:
                timeout *= 2
            to_map = next_to_map
        print(f'[{datetime.now()}] _new_permanent_pos_size: done')

    def _new_predicates(self) -> None:
        if self.m == 0:
            return
        new = range(len(self.predicate_vs[0]), len(self.predicates))
        if len(new) == 0:
            return
        for k in range(self.m):
            self.predicate_vs[k].extend(z3.Bool(f'p_{k}_{i}') for i in new)
            print(f'[{datetime.now()}] Mapping out subclauses-predicate interaction with {len(new)} new predicates for {self.to_clause(k, self.all_n[k])}')
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
                self.solver.add(self.predicate_vs[k][i] == z3.And(*(
                    z3.Or(*(
                        self.lit_vs[k][j] for j in sorted(self.all_n[k] - v)
                    ))
                    for v in all_mss
                )))
                total_mus += len(all_mus)
                total_mss += len(all_mss)
            print(f'[{datetime.now()}] Done subclauses-predicates (total_cdnf={total_mus + total_mss}, total_mus={total_mus}, total_mss={total_mss})')

    def separate(self,
                 size: Sequence[int],
                 pos: Collection[int] = (),
                 neg: Collection[int] = (),
                 imp: Collection[Tuple[int, int]] = (),
                 permanent_pos: Collection[int] = (), # indices into self.states for which the current and future separators must be true, must always be increasing w.r.t. previous calls
                 pos_ps: Collection[int] = (), # each clause must be implied by these predicates (used to force initiation)
                 neg_ps: Collection[int] = (), # each clause must not be implied by these predicates
    ) -> Optional[List[FrozenSet[int]]]:
        '''
        find a conjunction of subclauses that respects given constraints

        size should be of length self.m, and specifies the maximal number of literals in each clause

        TODO: to we need an unsat core in case there is no subclause?

        NOTE: the result must contain a subclause of each top clause, i.e., true cannot be used instead of one of the top clauses
        '''
        assert len(size) == self.m
        assert all(0 <= size[k] for k in range(self.m))
        size = [min(size[k], self.n[k]) for k in range(self.m)]
        assert all(0 <= i < len(self.states) for i in chain(pos, neg, chain(*imp), permanent_pos))
        assert all(0 <= i < len(self.predicates) for i in chain(pos_ps, neg_ps))
        permanent_pos = set(permanent_pos)
        assert self.permanent_pos <= permanent_pos
        self._new_permanent_pos_size(size, permanent_pos)
        self._new_states_size(
            size,
            list(chain(
                pos,
                neg,
                chain(*imp),
            )),
        )
        self._new_predicates()
        print(f'[{datetime.now()}] MultiSubclausesMapBySizeSep.separate: starting')
        sep = list(chain(
            (self.size_vs[k][size[k]] for k in range(self.m)),
            (z3.And(*(self.state_v(k, i) for k in range(self.m))) for i in sorted(pos)),
            (z3.Or(*(z3.Not(self.state_v(k, i)) for k in range(self.m))) for i in sorted(neg)),
            (z3.Implies(
                z3.And(*(self.state_v(k, i) for k in range(self.m))),
                z3.And(*(self.state_v(k, j) for k in range(self.m))),
            ) for i, j in sorted(imp)),
            (z3.And(*(self.predicate_vs[k][i] for k in range(self.m))) for i in sorted(pos_ps)),
            (z3.And(*(z3.Not(self.predicate_vs[k][i]) for k in range(self.m))) for i in sorted(neg_ps)),
        ))
        self.solver.push()
        for c in sep:
            self.solver.add(c)
        print(f'[{datetime.now()}] Checking MultiSubclausesMapBySizeSep.solver... ')
        t_start = datetime.now()
        res = self.solver.check()
        t_end = datetime.now()
        print(f'[{datetime.now()}] Checking MultiSubclausesMapBySizeSep.solver... got {res}')
        assert res in (z3.unsat, z3.sat)
        if (t_end - t_start).total_seconds() > 3600:
            smt2 = self.solver.to_smt2()
            fn = f'{sha1(smt2.encode()).hexdigest()}.sexpr'
            print(f'[{datetime.now()}] MultiSubclausesMapBySizeSep.separate: that took very long, saving saving query to {fn} ({len(smt2)} bytes)')
            open(fn, 'w').write(smt2)
        if res == z3.unsat:
            self.solver.pop()
            print(f'[{datetime.now()}] MultiSubclausesMapBySizeSep.separate: done')
            return None
        # minimize the number of quantifiers used, not sure how much this is needed, but as long as the solver is fast we can keep it
        for n in itertools.count():
            if utils.args.max_quantifiers is not None and n > utils.args.max_quantifiers:
                self.solver.pop()
                print(f'[{datetime.now()}] MultiSubclausesMapBySizeSep.separate: reached maximal number of quantifiers')
                print(f'[{datetime.now()}] MultiSubclausesMapBySizeSep.separate: done')
                return None
            self.solver.push()
            for k in range(self.m):
                self.solver.add(z3.AtMost(*self.var_vs[k], n))
            print(f'[{datetime.now()}] Checking MultiSubclausesMapBySizeSep.solver (optimizing quantifiers, n={n})... ')
            res = self.solver.check()
            print(f'[{datetime.now()}] Checking MultiSubclausesMapBySizeSep.solver (optimizing quantifiers, n={n})... got {res}')
            assert res in (z3.unsat, z3.sat)
            if res == z3.sat:
                model = self.solver.model()
                forced_to_false = [set(
                    i for i, v in enumerate(self.lit_vs[k])
                    if not z3.is_true(model[v])
                ) for k in range(self.m)]
                self.solver.pop()
                for k in range(self.m):
                    self.solver.add(z3.AtMost(*self.var_vs[k], n))
                break
            else:
                self.solver.pop()
        # minimize for strongest possible clause. TODO: should minimize size instead
        for k in range(self.m):
            for i in range(self.n[k]):
                if i not in forced_to_false[k]:
                    ki = [(kk, ii) for kk in range(self.m) for ii in forced_to_false[kk]] + [(k, i)]
                    print(f'[{datetime.now()}] Checking MultiSubclausesMapICE.solver (optimizing literals)... ')
                    res = self.solver.check(*(z3.Not(self.lit_vs[kk][ii]) for kk, ii in sorted(ki)))
                    print(f'[{datetime.now()}] Checking MultiSubclausesMapICE.solver (optimizing literals)... got {res}')
                    assert res in (z3.unsat, z3.sat)
                    if res == z3.sat:
                        model = self.solver.model()
                        for kk in range(self.m):
                            for ii, v in enumerate(self.lit_vs[k]):
                                if ii not in forced_to_false[kk] and not z3.is_true(model[v]):
                                    forced_to_false[kk].add(ii)
                        assert i in forced_to_false[k]
        ki = [(kk, ii) for kk in range(self.m) for ii in forced_to_false[kk]]
        assert self.solver.check(*(z3.Not(self.lit_vs[kk][ii]) for kk, ii in sorted(ki))) == z3.sat # TODO: remove assertion after we are confident about this code
        result = [frozenset(self.all_n[k] - forced_to_false[k]) for k in range(self.m)]
        assert all(len(result[k]) <= size[k] for k in range(self.m)), (size, result)
        self.solver.pop()
        print(f'[{datetime.now()}] MultiSubclausesMapBySizeSep.separate: done')
        return result

    def to_clause(self, k: int, s: Iterable[int]) -> Expr:
        s = sorted(s)
        assert 0 <= k < self.m, (k, s, self.m, self.n)
        assert all(0 <= i < self.n[k] for i in s), (k, s, self.m, self.n)
        lits = [self.literals[k][i] for i in s]
        free = set(chain(*(free_ids(lit) for lit in lits)))
        vs = tuple(v for v in self.variables[k] if v.name in free)
        return Forall(vs, Or(*lits)) if len(vs) > 0 else Or(*lits)


def forward_explore_marco_turbo(solver: Solver,
                                clauses: Sequence[Expr],
                                _states: Optional[Iterable[PDState]] = None
) -> Tuple[List[PDState], Sequence[Expr]]:

    prog = syntax.the_program
    # inits = tuple(init.expr for init in prog.inits())
    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # must be in CNF for use in eval_in_state

    states: List[PDState] = [] if _states is None else list(_states)
    predicates: List[Expr] = []  # growing list of predicates considered
    live: FrozenSet[int] = frozenset()  # indices into predicates for predicates p s.t. init U states |= p /\ wp(p)

    def alpha_live(states: Collection[PDState]) -> Sequence[Expr]:
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
                          _states: Optional[Iterable[PDState]] = None
) -> Tuple[List[PDState], Sequence[Expr]]:

    prog = syntax.the_program
    states: List[PDState] = [] if _states is None else list(_states)

    # inits = tuple(init.expr for init in prog.inits())
    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # must be in CNF for use in eval_in_state

    class SubclausesMap:
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
            free = set(chain(*(free_ids(lit) for lit in lits)))
            vs = tuple(v for v in self.variables if v.name in free)
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

    ########################################################
    # TODO: here lies commented out the version that uses one big
    # solver, since it does not use caches appropriately. Maybe we
    # should bring this back at some point
    #
    # wp_valid_solver = Solver()
    # t = wp_valid_solver.get_translator(2)
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
    #             z3.And(lit_indicators[i], t.translate_expr(lit, index=1))
    #             for i, lit in enumerate(mp.literals)
    #         ))
    #     wp_valid_solver.add(z3.Implies(mp_indicators[mp], z3.Not(z3.ForAll(bs, body))))
    # init_indicator = z3.Bool('@init')
    # for init in prog.inits():
    #     wp_valid_solver.add(z3.Implies(init_indicator, t.translate_expr(init.expr, index=0)))
    # precondition_indicators: Dict[Optional[PDState], z3.ExprRef] = {None: init_indicator}
    # def precondition_indicator(precondition: Optional[PDState]) -> z3.ExprRef:
    #     if precondition not in precondition_indicators:
    #         assert precondition is not None
    #         x = z3.Bool(f'@state_{id(precondition)})')
    #         wp_valid_solver.add(z3.Implies(x, t.translate_expr(precondition.as_onestate_formula(0), index=0)))
    #         precondition_indicators[precondition] = x
    #     return precondition_indicators[precondition]
    # transition_indicators = []
    # for i, trans in enumerate(prog.transitions()):
    #     transition_indicators.append(z3.Bool(f'@transition_{i}'))
    #     wp_valid_solver.add(z3.Implies(transition_indicators[i], t.translate_expr(trans.as_twostate_formula(prog.scope))))
    # wp_checked_valid: Set[Tuple[Optional[PDState], SubclausesMap, Tuple[int,...]]] = set()
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
    #                 prestate = Trace.from_z3((KEY_OLD,), z3model)
    #                 poststate = Trace.from_z3([KEY_NEW, KEY_OLD], z3model)
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
    #             t.translate_expr(mp.to_clause(s), index=1)
    #         ))

    #     return True
    ########################################################

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
                    alpha: Callable[[Collection[PDState]], Sequence[Expr]],
                    states: Optional[Iterable[PDState]] = None
) -> Tuple[List[PDState], Sequence[Expr], List[int], List[Tuple[int, int]]]:
    '''
    forward exploration from given states
    result is: more_states, a, initial, transitions
    more_states is an extension of states
    a is the abstract value of more_states
    initial are indicies to more_states of initial states
    transitions are indicies to more_states of transitions
    '''
    # TODO: make cleanup pass and reduce printing (added when adding BMC unrolling)
    res: Optional[Tuple[PDState,...]] = None

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
            (s for s in states if s.num_states == 1), # discovered initial states
            [None], # general initial state
            (s for s in states if s.num_states > 1) # discovered non-initial states
        )
        def label(s: Optional[PDState]) -> str:
            return 'init' if s is None else 'initial state' if s.num_states == 1 else 'state'
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
            (s for s in states if s.num_states == 1), # discovered initial states
            [None], # general initial state
            (s for s in states if s.num_states > 1) # discovered non-initial states
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
    def alpha_inv(states: Iterable[PDState]) -> Sequence[Expr]:
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
    reachable_states : List[PDState] = []

    # TODO: get this from command line option, and from the right file
    # with open('reachable-states.cache', 'rb') as cache_file:
    #     reachable_states = tuple(pickle.load(cache_file))
    # print('initialized reachable states:')
    # for m in reachable_states:
    #     print(str(m) + '\n' + '-'*80)

    clauses : List[Expr] = list(chain(*(as_clauses(x) for x in safety)))  # all top clauses in our abstraction
    sharp_predicates : Sequence[Expr] = ()  # the sharp predicates (minimal clauses true on the known reachable states)
    def alpha_clauses(states: Collection[PDState]) -> Sequence[Expr]:
        return sorted(
            dedup_equivalent_predicates(s, chain(*(alpha_from_clause(s, states, clause) for clause in clauses))),
            key=lambda x: (len(str(x)),str(x))
        )
    def alpha_sharp(states: Collection[PDState]) -> Sequence[Expr]:
        return sorted(
            alpha_from_predicates(s, states, sharp_predicates),
            key=lambda x: (len(str(x)),str(x))
        )
    def forward_explore_clauses(states: Iterable[PDState]) -> Tuple[List[PDState], Sequence[Expr]]:
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
                cs = as_clauses(Not(Diagram(m.as_state(0)).to_ast()))
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

    states: List[PDState] = []
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

    def add_state(s: PDState) -> int:
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
        cs = as_clauses(Not(Diagram(s.as_state(0)).to_ast()))
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

    def alpha_sharp(states: Collection[PDState]) -> Sequence[Expr]:
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
        def alpha_a(states: Collection[PDState]) -> Sequence[Expr]:
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

    states: List[PDState] = []
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

    def add_state(s: PDState) -> int:
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
            cs = as_clauses(Not(Diagram(s.as_state(0)).to_ast()))
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

    def alpha_sharp(states: Collection[PDState]) -> Sequence[Expr]:
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
        def alpha_a(states: Collection[PDState]) -> Sequence[Expr]:
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

    states: List[PDState] = []
    maps: List[SubclausesMapTurbo] = []  # for each state, a map with the negation of its diagram
    # the following are indices into states:
    reachable: FrozenSet[int] = frozenset()
    live_states: FrozenSet[int] = frozenset() # not yet ruled out by invariant
    transitions: List[Tuple[int, int]] = [] # TODO: maybe should be frozenset
    substructure: List[Tuple[int, int]] = [] # TODO: maybe should be frozenset

    def add_state(s: PDState) -> int:
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
        cs = as_clauses(Not(Diagram(s.as_state(0)).to_ast()))
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

    def alpha_sharp(states: Collection[PDState]) -> Sequence[Expr]:
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
        def alpha_a(states: Collection[PDState]) -> Sequence[Expr]:
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

    print(f'\n[{datetime.now()}] [PID={os.getpid()}] Starting primal_dual_houdini\n')

    safety = tuple(chain(*(as_clauses(inv.expr) for inv in prog.invs() if inv.is_safety))) # conver to CNF
    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # convert to CNF
    init_ps = [And(*inits)] # to be used with MultiSubclausesMapICE
    assert cheap_check_implication(inits, safety), 'Initial states not safe'

    states: List[PDState] = [] # used both for the high level houdini states (reachable, live_states) and the internal CTIs of the "dual edge solver" (internal_ctis)
    states_of_fingerprint: Dict[State.Fingerprint, List[int]] = defaultdict(list)
    maps: List[MultiSubclausesMapBySizeSep] = []  # for each state, a MultiSubclausesMapBySizeSep map with only the negation of its diagram. used in several places either to get the negation of the state's diagram or to find a clause that excludes it (mostly when finding p's, I think)
    _maps: Dict[Tuple[Expr,...], MultiSubclausesMapBySizeSep] = dict() # a cache of MultiSubclausesMapBySizeSep indexed by top_clauses
    find_dual_edge_ctis: Dict[Tuple[Expr,...], FrozenSet[int]] = defaultdict(frozenset) # keep a set of useful ctis for each goals in find_dual_edge
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

    human_invariant = tuple(chain(*(as_clauses(inv.expr) for inv in prog.invs()))) # convert to CNF
    human_invariant_to_predicate: Dict[int,int] = dict() # dict mapping index of human_invariant to index of predicates
    human_invariant_proved: Set[int] = set() # indices into human_invariant that are implied by the current inductive_invariant
    human_invariant_implies: Set[int] = set() # indices into predicates of predicates that are implied by the human invariant
    max_size = max(len(destruct_clause(h)[1]) for h in human_invariant) # TODO: don't cheat
    print(f'[{datetime.now()}] primal_dual_houdini: max_size = {max_size}')

    # reason_for_predicate: Dict[int, FrozenSet[int]] = defaultdict(frozenset) # for each predicate index, the indices of the states it helps to exclude # TODO: maybe bring this back here, but some predicates are to rule out actual states, and some just for internal CTIs

    def save_algorithm_state() -> None:
        algorith_state = (
            states,
            states_of_fingerprint,
            find_dual_edge_ctis,
            reachable,
            live_states,
            internal_ctis,
            transitions,
            substructure,
            predicates,
            inductive_invariant,
            live_predicates,
            dual_transitions,
            frames,
            step_frames,
            dual_frames,
        )
        pd = pickle.dumps(algorith_state)
        fn = f'{sha1(pd).hexdigest()}.pd.gz'
        print(f'[{datetime.now()}] [PID={os.getpid()}] primal_dual_houdini: saving algorith state to {fn} ({len(pd)} bytes)')
        with gzip.open(fn, 'wb') as f:
            f.write(pd)

    def restart_from_file(fn: str) -> None:
        nonlocal reachable
        print(f'[{datetime.now()}] restart_from_file: loading algorithm state from {fn}')
        with gzip.open(fn, 'rb') as f:
            pd = f.read()
        print(f'[{datetime.now()}] restart_from_file: file {fn} read ({len(pd)} bytes)')
        # assert str(sha1(pd)) == fn.split('.')[0]
        algorith_state = pickle.loads(pd)
        print(f'[{datetime.now()}] restart_from_file: algorith state unpickled')
        (
            _states,
            _states_of_fingerprint,
            _find_dual_edge_ctis,
            _reachable,
            _live_states,
            _internal_ctis,
            _transitions,
            _substructure,
            _predicates,
            _inductive_invariant,
            _live_predicates,
            _dual_transitions,
            _frames,
            _step_frames,
            _dual_frames,
        ) = algorith_state

        # add all reachable states
        state_i: Dict[int, int] = dict()
        for n, i in enumerate(_reachable):
            print(f'[{datetime.now()}] restart_from_file: processing reachable state {n} / {len(_reachable)}')
            s = _states[i]
            ii = add_state(s, False)
            state_i[i] = ii
            if all(eval_in_state(None, s, p) for p in inits):
                _cache_initial.append(s)
                reachable |= {ii}
        print(f'[{datetime.now()}] restart_from_file: state_i = {state_i}')
        # add all transitions and substructures
        for i, j in _transitions:
            if i in _reachable and j in _reachable:
                add_transition(state_i[i], state_i[j])
                _cache_transitions.append((states[state_i[i]], states[state_i[j]]))
        assert reachable == frozenset(state_i[i] for i in _reachable), (reachable, _reachable)

        # add all invariant predicates
        predicate_i: Dict[int, int] = dict()
        for n, i in enumerate(_inductive_invariant):
            print(f'[{datetime.now()}] restart_from_file: processing invariant predicate {n} / {len(_inductive_invariant)}')
            p = _predicates[i]
            predicate_i[i] = add_predicate(p)
        print(f'[{datetime.now()}] restart_from_file: predicate_i = {predicate_i}')
        print(f'[{datetime.now()}] restart_from_file: done')
        print_status_and_check_termination()
        assert_invariants()

    def get_map(top_clauses: Tuple[Expr,...]) -> MultiSubclausesMapBySizeSep:
        if top_clauses not in _maps:
            _maps[top_clauses] = MultiSubclausesMapBySizeSep(top_clauses, states, init_ps)
        return _maps[top_clauses]

    def add_state(s: PDState, internal_cti: bool) -> int:
        nonlocal live_states
        nonlocal internal_ctis
        #production# assert all(eval_in_state(None, s, predicates[j]) for j in sorted(inductive_invariant))
        note = ' (internal cti)' if internal_cti else ' (live state)'
        print(f'[{datetime.now()}] add_state: starting')
        if s not in states:
            maybe_isomorphic = states_of_fingerprint[s.as_state(0).fingerprint]
            if len(maybe_isomorphic) > 0:
                print(f'[{datetime.now()}] add_state{note}: checking for isomorphism ({len(maybe_isomorphic)} candidates)... ')
            for j in maybe_isomorphic:
                if is_substructure(s, states[j]) and is_substructure(states[j], s):
                    print(f'[{datetime.now()}] add_state{note}: isomorphic to previous state: states[{j}]')
                    i = j
                    break
            else:
                print(f'[{datetime.now()}] add_state{note}: checking for substructures... ')
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
                if False:
                    for j in sorted(substructures):
                        if not states[j].as_state(0).maybe_substructure(states[i].as_state(0)):
                            print(states[i].as_state(0))
                            print(states[i].as_state(0).fingerprint)
                            print('\n\n\n')
                            print(states[j].as_state(0))
                            print(states[j].as_state(0).fingerprint)
                            assert False
                    for j in sorted(superstructures):
                        if not states[i].as_state(0).maybe_substructure(states[j].as_state(0)):
                            print(states[i].as_state(0))
                            print(states[i].as_state(0).fingerprint)
                            print('\n\n\n')
                            print(states[j].as_state(0))
                            print(states[j].as_state(0).fingerprint)
                            assert False
                print(f'[{datetime.now()}] add_state{note}: substructures={sorted(substructures)}, superstructures={sorted(superstructures)}')
                print(f'[{datetime.now()}] done')
                isomorphic = substructures & superstructures
                assert len(isomorphic) == 0
                i = len(states)
                states.append(s)
                states_of_fingerprint[s.as_state(0).fingerprint].append(i)
                substructure.extend((i, j) for j in sorted(substructures))
                substructure.extend((j, i) for j in sorted(superstructures))
                cs = as_clauses(Not(Diagram(s.as_state(0)).to_ast()))
                assert len(cs) == 1
                c = cs[0]
                maps.append(get_map((c,)))
                print(f'[{datetime.now()}] add_state{note}: adding new state: states[{i}], c={c}')
            if internal_cti:
                internal_ctis |= {i}
            else:
                live_states |= {i}
            print(f'[{datetime.now()}] add_state: done')
            return i
        else:
            i = states.index(s)
            if internal_cti:
                if i not in internal_ctis:
                    print(f'[{datetime.now()}] add_state{note}: adding states[{i}] to internal_ctis')
                    internal_ctis |= {i}
                else:
                    print(f'[{datetime.now()}] add_state{note}: already have states[{i}] in internal_ctis')
            else:
                if i not in live_states:
                    print(f'[{datetime.now()}] add_state{note}: adding states[{i}] to live_states')
                    live_states |= {i}
                else:
                    print(f'[{datetime.now()}] add_state{note}: already have states[{i}] in live_states')
            print(f'[{datetime.now()}] add_state: done')
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

    def _add_predicate(p: Predicate) -> int:
        nonlocal predicates
        nonlocal live_predicates
        nonlocal human_invariant_to_predicate
        nonlocal human_invariant_implies
        # nonlocal reason_for_predicate
        if p not in predicates:
            for j, q in enumerate(predicates):
                if cheap_check_implication([p], [q]) and cheap_check_implication([q], [p]):
                    print(f'[{datetime.now()}] add_predicate: equivalent to existing predicate {j}: {p} <=> {q}')
                    if j not in live_predicates:
                        print(f'[{datetime.now()}] add_predicate: reviving predicate {j}')
                    break
            else:
                j = len(predicates)
                print(f'[{datetime.now()}] add_predicate: adding new predicate {j}: {p}')
                predicates.append(p)
                if cheap_check_implication(human_invariant, [p]):
                    human_invariant_implies.add(j)
                    for i, q in enumerate(human_invariant):
                        if cheap_check_implication([p], [q]) and cheap_check_implication([q], [p]):
                            print(f'[{datetime.now()}] add_predicate: equivalent to human invariant predicate {i}: {p} <=> {q}')
                            assert i not in human_invariant_to_predicate
                            human_invariant_to_predicate[i] = j
                            break
                    else:
                        print(f'[{datetime.now()}] add_predicate: implied by human invariant: => {p}')

        else:
            j = predicates.index(p)
            if j in live_predicates:
                print(f'[{datetime.now()}] add_predicate: already have this predicate {j}: {p}')
            else:
                print(f'[{datetime.now()}] add_predicate: reviving previous predicate {j}: {p}')
        live_predicates |= {j}
        #TODO# assert all(eval_in_state(None, states[i], p) for i in sorted(reachable))
        # if reason is not None:
        #     assert False # maybe this will change later
        #     # reason_for_predicate[j] |= {reason}
        return j

    def add_predicate_and_subclauses(top_p: Predicate) -> int:
        for p in subclauses(top_p):
            if p != top_p and all(eval_in_state(None, states[i], p) for i in sorted(reachable)):
                _add_predicate(p)
        return _add_predicate(top_p)
    add_predicate = add_predicate_and_subclauses if utils.args.all_subclauses else _add_predicate

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
        print(f'[{datetime.now()}] forward_explore_from_states: starting')
        print(f'[{datetime.now()}] Starting forward_explore_from_states({sorted(src)})')
        nonlocal reachable
        r: FrozenSet[int] = reachable | src
        r = close_forward(r)
        a = [predicates[j] for j in sorted(live_predicates)]
        def alpha_a(states: Collection[PDState]) -> Sequence[Expr]:
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
        print(f'[{datetime.now()}] Finished forward_explore_from_states({sorted(src)})')
        print(f'[{datetime.now()}] forward_explore_from_states: done')

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

        print(f'[{datetime.now()}] houdini_frames: starting')

        # first forward_explore from the reachable states
        n_reachable = len(reachable)
        n_live_predicates = len(live_predicates)
        forward_explore_from_states(reachable)
        new_reachable_states()
        print(f'[{datetime.now()}] Forward explore of reachable states found {len(reachable) - n_reachable} new reachable states, eliminating {n_live_predicates - len(live_predicates)} predicates')
        assert_invariants()

        frames = [[predicates[i] for i in sorted(live_predicates)]]
        r = reachable
        while True:
            #production# assert r == close_forward(r)
            a = frames[-1]
            #production# assert all(eval_in_state(None, states[i], p) for i, p in product(sorted(r), a))
            for i in sorted(live_states):
                if i not in r and all(eval_in_state(None, states[i], p) for p in a):
                    r |= {i}
                    r = close_forward(r)
            n_reachable = len(reachable)
            forward_explore_from_states(r) # TODO: not sure if we should do this here or not
            #production# assert n_reachable == len(reachable)
            r = close_forward(r)
            for i in sorted(live_states):
                if i in r:
                    continue
                print(f'[{datetime.now()}] houdini_frames: checking for backward-transition from states[{i}]')
                res = check_two_state_implication(
                    solver,
                    a + [maps[i].to_clause(0, maps[i].all_n[0])],
                    maps[i].to_clause(0, maps[i].all_n[0]),
                    f'backward-transition from states[{i}]'
                )
                print(f'[{datetime.now()}] houdini_frames: done checking for backward-transition from states[{i}]')
                if res is not None:
                    prestate, poststate = res
                    i_pre = add_state(prestate, False)
                    i_post = add_state(poststate, False)
                    add_transition(i_pre, i_post)
                    #production# assert i_post == i or (i_post, i) in substructure
                    reachable = close_forward(reachable) # we could have learned that i_pre is reachable here.... TODO: this is inconsistent with frames, and this should be fixed
                    r |= {i_pre}
                    r = close_forward(r)
            n_reachable = len(reachable)
            forward_explore_from_states(r) # this is probably a good place for this
            #production# assert n_reachable == len(reachable)
            r = close_forward(r)
            b = [p for p in a if all(eval_in_state(None, states[i], p) for i in sorted(r))]
            for p in b[:]:
                if p not in b or predicates.index(p) in inductive_invariant:
                    continue
                print(f'[{datetime.now()}] houdini_frames: checking for CTI to {p}')
                res = check_two_state_implication(solver, a, p, 'CTI')
                print(f'[{datetime.now()}] houdini_frames: done checking for CTI to {p}')
                if res is not None:
                    prestate, poststate = res
                    i_pre = add_state(prestate, False)
                    i_post = add_state(poststate, False)
                    if (i_pre, i_post) not in transitions:
                        add_transition(i_pre, i_post)
                        reachable = close_forward(reachable) # we could have learned that i_pre is reachable here.... TODO: this is inconsistent with frames, and this should be fixed
                    else:
                        #production# assert i_pre not in r
                        pass
                    r |= {i_pre}
                    r = close_forward(r)
                    n_reachable = len(reachable)
                    forward_explore_from_states(r) # this is probably a good place for this
                    #production# assert n_reachable == len(reachable)
                    r = close_forward(r)
                    b = [p for p in b if all(eval_in_state(None, states[i], p) for i in sorted(r))]
            if a == b:
                break
            else:
                frames.append(b)
        # here, frames[-1] is inductive (but it may not imply safety)
        #production# assert frames[-1] == a == b
        inv = frozenset(predicates.index(p) for p in a)
        #production# assert inductive_invariant <= inv
        inductive_invariant = inv
        print(f'[{datetime.now()}] houdini_frames: done')

    def compute_step_frames() -> None:
        nonlocal step_frames
        print(f'[{datetime.now()}] compute_step_frames: starting')
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
        #production# assert step_frames[-1] == a == b
        inv = frozenset(predicates.index(p) for p in a)
        #production# assert inductive_invariant == inv
        print(f'[{datetime.now()}] compute_step_frames: done')

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
        print(f'[{datetime.now()}] dual_houdini_frames: starting')
        # first forward_explore from the current inductive invariant
        n_inductive_invariant = len(inductive_invariant)
        n_reachable_states = len(reachable)
        forward_explore_from_predicates(inductive_invariant)
        new_inductive_invariants()
        new_reachable_states()
        print(f'[{datetime.now()}] dual_houdini_frames: forward explore of inductive invariant found {len(inductive_invariant) - n_inductive_invariant} new inductive predicates and {len(reachable) - n_reachable_states} new reachable states')
        assert_invariants()
        # TODO: should we stop here in case we found anything and go back to primal houdini?

        dual_frames = [sorted(live_states)]
        # TODO: there is a consistency problem if new reachable states are discovered during the loop, since they will not be part of previous frames, this should be figured out, maybe by restarting everything if we find a new reachable state
        r = inductive_invariant
        while True:
            #production# assert r == dual_close_forward(r)
            a = dual_frames[-1]
            #production# assert all(eval_in_state(None, states[i], predicates[j]) for i, j in product(a, sorted(r)))
            print(f'[{datetime.now()}] dual_houdini_frames: starting iteration, r={sorted(r)}, a=reachable+{sorted(frozenset(a) - reachable)}')
            r_0 = r
            for j in sorted(live_predicates):
                if j not in r and all(eval_in_state(None, states[i], predicates[j]) for i in a):
                    print(f'[{datetime.now()}] dual_houdini_frames: adding {j} to r by abstract implication')
                    r |= {j}
                    r = dual_close_forward(r)
            n_reachable = len(reachable)
            n_inductive_invariant = len(inductive_invariant)
            # forward_explore_from_predicates(r) # TODO: not sure if we should do this here or not # ODED'21: removed this to experiment
            #TODO# assert n_reachable == len(reachable), '?' see sharded-kv-retransmit.pd-primal-dual-houdini.dfc198b.seed-1234.log
            #TODO# assert n_inductive_invariant == len(inductive_invariant), '?' sharded-kv-retransmit_unsafe.pd-primal-dual-houdini.daf032c.seed-1234.log paxos_forall_choosable.pd-primal-dual-houdini.daf032c.seed-0.log
            r = dual_close_forward(r)
            # try to add edges to existing predicates (dual-backward-transitions)
            goals = live_predicates - r
            if len(goals) > 0:
                print(f'[{datetime.now()}] dual_houdini_frames: checking for dual-backward-transition from predicates{sorted(goals)}')
                res = find_dual_backward_transition(
                    a,
                    r_0,  # ODED'21: not clear why this is r_0 and not r
                    goals,
                )
                print(f'[{datetime.now()}] dual_houdini_frames: done checking for dual-backward-transition predicates{sorted(goals)}')
                if res is not None:
                    ps = frozenset(add_predicate(p) for p in res[0])
                    qs = frozenset(add_predicate(q) for q in res[1]) # should not add any new predicates actually
                    assert qs <= goals
                    assert len(qs) > 0
                    dual_transitions.append((ps, qs))
                    n_inductive_invariant = len(inductive_invariant)
                    inductive_invariant = dual_close_forward(inductive_invariant)
                    #TODO# assert n_inductive_invariant == len(inductive_invariant) # TODO: maybe we actually learned a new inductive invariant. this will be inconsisted with the frames, as in primal houdini_frames
                    r |= ps
                    r = dual_close_forward(r)
                    #production# assert qs <= r
            # here lies commented out the version without find_dual_backward_transition
            # for j in sorted(live_predicates):
            #     if j in r:
            #         continue
            #     print(f'[{datetime.now()}] dual_houdini_frames: checking for dual-backward-transition from predicates[{j}]: {predicates[j]}')
            #     res = find_dual_edge(
            #         a,
            #         r_0,
            #         predicates[j],
            #         [states[i] for i in a
            #          if all(eval_in_state(None, states[i], predicates[j]) for j in sorted(r))
            #         ], # TODO: change this when find_dual_edge supports greedy predicate goals
            #     )
            #     print(f'[{datetime.now()}] dual_houdini_frames: done checking for dual-backward-transition from predicates[{j}]: {predicates[j]}')
            #     if res is not None:
            #         ps = frozenset(add_predicate(p) for p in res[0])
            #         qs = frozenset(add_predicate(q) for q in res[1])
            #         dual_transitions.append((ps, qs))
            #         assert cheap_check_implication(res[1], [predicates[j]])
            #         n_inductive_invariant = len(inductive_invariant)
            #         inductive_invariant = dual_close_forward(inductive_invariant)
            #         #TODO# assert n_inductive_invariant == len(inductive_invariant) # TODO: maybe we actually learned a new inductive invariant. this will be inconsisted with the frames, as in primal houdini_frames
            #         r |= ps
            #         r = dual_close_forward(r)
            #         assert qs <= r
            n_inductive_invariant = len(inductive_invariant)
            # forward_explore_from_predicates(r) # this is probably a good place for this # ODED'21: no it isn't! there's no difference from the last time. # ODED'21: removed this to experiment
            #TODO# assert n_reachable == len(reachable), '?'
            #production# assert n_inductive_invariant == len(inductive_invariant), '?'
            r = dual_close_forward(r)
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
                print(f'[{datetime.now()}] dual_houdini_frames: trying to eliminate the following {len(roots)} roots: {sorted(roots)}')
                for i in sorted(roots):
                    #TODO# assert i not in reachable ??? see paxos_forall.pd-primal-dual-houdini.5e0ed39.seed-1234.log
                    if i in reachable:
                        continue
                    if not all(eval_in_state(None, states[i], predicates[j]) for j in sorted(r)):
                        # already eliminated i
                        #production# assert changes
                        continue
                    print(f'[{datetime.now()}] dual_houdini_frames: checking for dual-CTI to states[{i}]')
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
                    print(f'[{datetime.now()}] dual_houdini_frames: done checking for dual-CTI to states[{i}]')
                    if res is not None:
                        ps = frozenset(add_predicate(p) for p in res[0])
                        qs = frozenset(add_predicate(q) for q in res[1])
                        dual_transitions.append((ps, qs))
                        n_inductive_invariant = len(inductive_invariant)
                        inductive_invariant = dual_close_forward(inductive_invariant)
                        #production# assert n_inductive_invariant == len(inductive_invariant) # TODO: maybe we actually learned a new inductive invariant. this will be inconsisted with the frames, as in primal houdini_frames
                        r |= ps
                        r = dual_close_forward(r)
                        #production# assert qs <= r
                        n_reachable = len(reachable)
                        n_inductive_invariant = len(inductive_invariant)
                        # forward_explore_from_predicates(r)  # this is probably a good place for this, note this may find a new inductive invariant, which is inconsistent with the frames, as in primal houdini_frames (I think) # ODED'21: removed this to experiment
                        #TODO# assert n_reachable == len(reachable), '?'
                        #TODO# assert n_inductive_invariant == len(inductive_invariant), '?'
                        r = dual_close_forward(r)
                        #production# assert not all(eval_in_state(None, states[i], predicates[j]) for j in sorted(r))
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
            print(f'[{datetime.now()}] dual_houdini_frames: next frame is: {sorted(b)}')
            if a == b:
                break
            else:
                dual_frames.append(b)
        # here, dual_frames[-1] should be the reachable states
        #production# assert dual_frames[-1] == a == b, (dual_frames[-1], a, b)
        # we need to update reachable to include everything reachable via transitions and substructures to internal CTIs, TODO: think more carefully about this
        reachable = close_forward(reachable, True)
        live_states |= reachable
        # TODO: this assertion is actually not true when there is a
        # cycle of unreachable states, we should think about it more
        # assert frozenset(dual_frames[-1]) <= reachable, sorted(frozenset(dual_frames[-1]) - reachable)
        print(f'[{datetime.now()}] dual_houdini_frames: done')
        print(f'[{datetime.now()}] dual_houdini_frames computed {len(dual_frames)} dual frames:')
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
        print(f'[{datetime.now()}] compute_roots: starting with: s={sorted(s)}, pos=reachable+{sorted(pos - reachable)}, ps={sorted(predicates.index(p) for p in ps)}, a={sorted(a) if a is not None else None}')
        # assert a is None or reachable <= a TODO: this can be violated if a new reachable state is discovered in dual_houdini_frames, think about this
        #production# assert reachable <= pos
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
            dom = frozenset(range(len(states))) # ODED'21: NB: we're using all states, not only live ones, i.e., including internal ctis
        dom = frozenset(i for i in dom if all(
            eval_in_state(None, states[i], p) for p in ps  # ODED'21: this filtering is unclear to me
        ))
        z3s = z3.Solver()
        for i in sorted(pos):
            z3s.add(v(i))
        for i, j in sorted(chain(transitions, substructure)):
            if i in dom and j in dom:
                z3s.add(z3.Implies(v(i), v(j)))
        z3s.add(z3.Or(*(z3.Not(v(i)) for i in sorted(s))))
        # print(f'[{datetime.now()}] compute_roots: z3s:\n{z3s}')
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
        print(f'[{datetime.now()}] compute_roots: s={sorted(s)}, pos=reachable+{sorted(pos - reachable)}, ps={sorted(predicates.index(p) for p in ps)}, a={sorted(a) if a is not None else None}, result is {sorted(r)}')
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
        print(f'[{datetime.now()}] forward_explore_from_predicates: starting')
        print(f'[{datetime.now()}] forward_explore_from_predicates: starting with predicates{sorted(src)}')
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
            # this is actually a (primal) Houdini process -- interesting TODO: think about it
            # TODO: maybe stratify this Houdini process
            qs = live_predicates - r
            while len(qs) > 0:
                cti, ps = check_dual_edge(
                    solver,
                    tuple(predicates[j] for j in sorted(r)),
                    tuple(predicates[j] for j in sorted(qs)),
                    # msg='cti?', TODO
                )
                if cti is None:
                    assert ps is not None
                    ps_i = frozenset(predicates.index(p) for p in ps)
                    #production# assert ps_i <= r
                    dual_transitions.append((ps_i, qs))
                    #production# assert not qs <= r
                    r = dual_close_forward(r)
                    #production# assert qs <= r
                    changes = True
                    print(f'[{datetime.now()}] forward_explore_from_predicates: connecting to existing predicates: predicates{sorted(qs)}')
                    break
                else:
                    prestate, poststate = cti
                    n_qs = len(qs)
                    qs = frozenset(j for j in qs if eval_in_state(None, poststate, predicates[j]))
                    #production# assert len(qs) < n_qs
            # here lies commented out the code that did not do this internal Houdini, and was faithful to induction width of 1:
            # for j in sorted(live_predicates):
            #     if j in r:
            #         continue
            #     cti, ps = check_dual_edge(
            #         solver,
            #         tuple(predicates[k] for k in sorted(r)),
            #         (predicates[j],),
            #         # msg='cti?', TODO
            #     )
            #     if cti is None:
            #         assert ps is not None
            #         ps_i = frozenset(predicates.index(p) for p in ps)
            #         assert ps_i <= r
            #         dual_transitions.append((ps_i, frozenset([j])))
            #         r = dual_close_forward(r)
            #         assert j in r
            #         changes = True
            if changes:
                continue
            # now try to find a concrete edge to a new predicate
            # find roots, and try to eliminate them
            #production# assert reachable == close_forward(reachable)
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
                print(f'[{datetime.now()}] forward_explore_from_predicates: trying to eliminate the following {len(roots)} roots: {sorted(roots)}')
            # try to find a new predicate that eliminates a root and is inductive relative to r
            for i in sorted(roots):
                #TODO# assert i not in reachable, i # TODO: see paxos_forall_choosable.pd-primal-dual-houdini.6d3c0fd.seed-5678.log
                if i in reachable:
                    continue
                print(f'[{datetime.now()}] forward_explore_from_predicates: checking for edge to eliminate states[{i}]')
                res = find_dual_edge([], r, states[i], [states[i] for i in sorted(to_eliminate)], n_ps=0)
                print(f'[{datetime.now()}] forward_explore_from_predicates: done checking for edge to eliminate states[{i}]')
                if res is not None:
                    ps_i = frozenset(add_predicate(p) for p in res[0])
                    qs_i = frozenset(add_predicate(q) for q in res[1])
                    #production# assert ps_i <= r
                    #production# assert not all(eval_in_state(None, states[i], predicates[j]) for j in qs_i)
                    dual_transitions.append((ps_i, qs_i))
                    r = dual_close_forward(r)
                    #production# assert qs_i <= r
                    print(f'[{datetime.now()}] forward_explore_from_predicates: connecting to new predicates: predicates{sorted(qs_i)}')
                    changes = True
                    break # to prioritize using existing predicates (no stratification, unlike in dual_houdini_frames)
            else:
                if False:
                    # just to find bugs in compute_roots
                    # TODO: run this sometime on all examples
                    for i in sorted(live_states):
                        if i in reachable or not all(eval_in_state(None, states[i], predicates[j]) for j in sorted(r)):
                            continue
                        assert find_dual_edge([], r, states[i], [], n_ps=0) is None, i
        # here there are no more dual edges that can be added
        inductive_invariant = dual_close_forward(inductive_invariant)
        print(f'[{datetime.now()}] forward_explore_from_predicates: finished exploring from predicates{sorted(src)}, found {len(r) - n_r} new provable predicates: predicates{sorted(r - src)}, and added {len(inductive_invariant) - n_inductive_invariant} new predicates to the inductive invariant')
        print(f'[{datetime.now()}] forward_explore_from_predicates: done')

    def find_dual_edge(
            pos: Collection[int], # indices into states that ps must satisfy
            r: Collection[int], # indices into predicates that can be used (assumed invariants)
            goal: Union[PDState, Predicate], # state to exclude or predicate to prove TODO: actually no need for predicates here, they are handled by find_dual_backward_transition
            soft_goals: Collection[PDState], # more states to exclude greedily, TODO: also support greedily proving predicates
            n_ps: Optional[int] = None, # None means unbounded, 0 means no such predicates beyond what is in r, for now no other bounds are supported
#            n_qs: int = 1,
    ) -> Optional[Tuple[Tuple[Predicate,...], Tuple[Predicate,...]]]:
        '''
        May add new reachable states if it finds new initial states
        '''
        print(f'[{datetime.now()}] find_dual_edge: starting')
        # n_qs = 3 # just for testing and messing around
        n_qs = utils.args.induction_width
        worklist_budget = 100
        nonlocal reachable
        pos = frozenset(pos)
        assert n_ps in (0, None) # for now we do not support finite bounds, either 0 or unbounded
        assert n_qs >= 1
        if n_ps == 0:
            assert len(pos) == 0
        # for now we don't support predicate soft_goals at all
        soft_goals_i = sorted(states.index(g) for g in soft_goals)
        stateof: Dict[Expr, int] = {}
        if isinstance(goal, PDState):
            goal_i = states.index(goal)
            goal = maps[goal_i].to_clause(0, maps[goal_i].all_n[0])
            stateof[goal] = goal_i
            print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: starting, pos={sorted(pos)}, r={sorted(r)}, goal=states[{goal_i}], soft_goals=states{soft_goals_i}, n_qs={n_qs}')
        else:
            print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: starting, pos={sorted(pos)}, r={sorted(r)}, goal=[{goal}], soft_goals=states{soft_goals_i}, n_qs={n_qs}')
        n_internal_ctis = len(internal_ctis)
        n_ctis = 0
        n_reachable = len(reachable)
        ps: List[Predicate] = [predicates[j] for j in sorted(r)]
        worklist: List[Tuple[Expr,...]] = [(goal,)]
        seen_before: FrozenSet[FrozenSet[Expr]] = frozenset()
        while len(worklist) > 0 and worklist_budget > 0:
            print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: worklist is {len(worklist)} long, budget is {worklist_budget}:')
            for goals in worklist:
                notes = ', '.join(f'states[{stateof[g]}]' if g in stateof else str(g) for g in goals)
                print(f'    ({notes}, )')
            print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: trying the top one')
            goals = worklist.pop(0)
            if frozenset(goals) in seen_before:
                print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: already seen this one, skipping')
                continue
            worklist_budget -= 1
            seen_before |= {frozenset(goals)}

            mp = get_map(goals)
            n_literals = sum(mp.n)
            size: int = 1
            def check_sep(s: Collection[int]) -> Optional[Tuple[List[Predicate], List[FrozenSet[int]]]]:
                s = frozenset(s) | reachable
                res = mp.separate(
                    tuple(size for _ in range(mp.m)),
                    permanent_pos=sorted(reachable),
                    # imp=sorted((i, j) for i, j in chain(transitions, substructure) if i in s and j in s),
                    imp=sorted((i, j) for i, j in transitions if i in s and j in s), # ODED: I think we don't need substructures here since for them the implication must hold anyway
                    pos_ps=[0],
                    # soft_neg=soft_goals_i,
                )
                if res is None:
                    return None
                else:
                    assert len(res) == mp.m == len(goals)
                    return [mp.to_clause(k, res[k]) for k in range(mp.m)], res
            # set up a cti_solver for fast and greedy discovery of ctis (alternative to check_dual_edge)
            # TODO: share this across different worklist items
            cti_solver = Solver() # TODO: maybe solver per transition
            t = cti_solver.get_translator(2)
            lit_indicators_pre =[[z3.Bool(f'@lit_pre_{k}_{i}') for i in range(mp.n[k])] for k in range(mp.m)]
            lit_indicators_post =[[z3.Bool(f'@lit_post_{k}_{i}') for i in range(mp.n[k])] for k in range(mp.m)]
            q_indicators_post = [z3.Bool(f'@q_post_{k}') for k in range(mp.m)]
            #
            # note - the polarity of lit_indicators_pre is negative,
            # it means the literal is not in the clause, unlike for
            # lit_indicators_post
            #
            # there is some craziness here about mixing a mypyvy clause with z3 indicator variables
            # some of this code is taken out of syntax.Z3Translator.translate_expr
            #
            for k in range(mp.m):
                top_clause = mp.to_clause(k, mp.all_n[k])
                assert top_clause == goals[k]
                bs = t.bind(top_clause.binder) if isinstance(top_clause, QuantifierExpr) else []
                assert len(bs) == len(mp.variables[k])
                # add the clause defined by lit_indicators_pre to the prestate
                with (t.scope.in_scope(top_clause.binder, bs)
                      if isinstance(top_clause, QuantifierExpr) else nullcontext()):
                    body = z3.Or(*(
                        z3.And(z3.Not(lit_indicators_pre[k][i]), t.translate_expr(lit)) # NB: polarity
                        for i, lit in enumerate(mp.literals[k])
                    ))
                e = z3.ForAll(bs, body) if len(bs) > 0 else body
                cti_solver.add(e)
                # add the negation of the clause defined by lit_indicators_post to the poststate, guarded by a q_indicator
                with (t.scope.in_scope(top_clause.binder, bs)
                      if isinstance(top_clause, QuantifierExpr) else nullcontext()):
                    body = z3.Or(*(
                        z3.And(lit_indicators_post[k][i], t.translate_expr(New(lit)))
                        for i, lit in enumerate(mp.literals[k])
                    ))
                e = z3.ForAll(bs, body) if len(bs) > 0 else body
                cti_solver.add(z3.Implies(q_indicators_post[k], z3.Not(e)))
            # add transition indicators
            transition_indicators: List[z3.ExprRef] = []
            for i, trans in enumerate(prog.transitions()):
                transition_indicators.append(z3.Bool(f'@transition_{i}_{trans.name}'))
                cti_solver.add(z3.Implies(transition_indicators[i], t.translate_expr(trans.as_twostate_formula(prog.scope))))
            p_indicators: List[z3.ExprRef] = []
            def cti_solver_add_p(p: Predicate) -> None:
                i = len(p_indicators)
                assert ps[i] == p
                p_indicators.append(z3.Bool(f'@p_{i}'))
                cti_solver.add(z3.Implies(p_indicators[i], t.translate_expr(p)))
                cti_solver.add(z3.Implies(p_indicators[i], t.translate_expr(New(p))))
            for p in ps:
                cti_solver_add_p(p)
            def add_p(p: Predicate) -> None:
                assert p not in ps
                ps.append(p)
                cti_solver_add_p(p)
            def check_q(q_seed: List[FrozenSet[int]], ps_seed: FrozenSet[int], optimize: bool = True) -> Optional[Tuple[PDState, PDState]]:
                for q_indicator, transition_indicator in product(q_indicators_post, transition_indicators):
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_q (find_dual_edge): testing {q_indicator}, {transition_indicator}')
                    indicators = tuple(chain(
                        [q_indicator, transition_indicator],
                        (lit_indicators_pre[k][i] for k in range(mp.m) for i in sorted(mp.all_n[k] - q_seed[k])),
                        (lit_indicators_post[k][i] for k in range(mp.m) for i in sorted(q_seed[k])),
                        (p_indicators[i] for i in sorted(ps_seed)),
                    ))
                    z3res = cti_solver.check(indicators)
                    assert z3res in (z3.sat, z3.unsat)
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_q (find_dual_edge): {z3res}')
                    if z3res == z3.unsat:
                        continue
                    if optimize:
                        # maximize indicators, to make for a more informative cti
                        for extra in chain(
                                # priorities: post, pre, ps
                                (lit_indicators_post[k][i] for k in range(mp.m) for i in sorted(mp.all_n[k] - q_seed[k])),
                                (lit_indicators_pre[k][i] for k in range(mp.m) for i in sorted(q_seed[k])),
                                (p_indicators[i] for i in range(len(p_indicators)) if i not in ps_seed),
                        ):
                            z3res = cti_solver.check(indicators + (extra,))
                            assert z3res in (z3.sat, z3.unsat)
                            if z3res == z3.sat:
                                print(f'[{datetime.now()}] [PID={os.getpid()}] check_q (find_dual_edge): adding extra: {extra}')
                                indicators += (extra,)
                        assert cti_solver.check(indicators) == z3.sat
                    prestate, poststate = unpack_cti(cti_solver.model(indicators))
                    print(f'[{datetime.now()}] [PID={os.getpid()}] check_q (find_dual_edge): found new cti violating dual edge')
                    _cache_transitions.append((prestate, poststate))
                    for state in (prestate, poststate):
                        if all(eval_in_state(None, state, p) for p in inits):
                            _cache_initial.append(state)
                    return prestate, poststate
                return None
            ctis: FrozenSet[int] = find_dual_edge_ctis[goals]
            while True:
                while True: # find a Q or discover there is none and learn internal_ctis
                    if False:
                        # use all previously known internal_ctis
                        ctis = frozenset(
                            i for i in sorted((live_states | internal_ctis) - reachable)
                            if all(eval_in_state(None, states[i], p) for p in ps)
                        )
                    else:
                        # use only ctis discovered for this worklist item (i.e., this mp)
                        ctis = frozenset(
                            i for i in sorted(ctis - reachable)
                            if all(eval_in_state(None, states[i], p) for p in ps)
                        )
                    res = check_sep(ctis)
                    if res is None:
                        break
                    q, q_seed = res
                    assert len(q) == len(q_seed) == len(goals) == mp.m
                    # here, q is a predicate such that r /\ ps /\ q |= wp(r /\ ps -> q) has no CTI in live_states | internal_ctis
                    # first, check if init |= q, if not, we learn a new initial state
                    if len(q) == 1:
                        print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: potential q is ({len(destruct_clause(q[0])[1])} literals): {q[0]}')
                    else:
                        print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: potential q is:')
                        for k in range(mp.m):
                            print(f'  ({len(destruct_clause(q[k])[1])} literals): {q[k]}')
                    initial = True
                    for qq in q:
                        s = check_initial(solver, qq)
                        if s is not None:
                            assert False # TODO: remove all this to simplify the code
                            initial = False
                            print(f'  this predicate is not initial, learned a new initial state')
                            i = add_state(s, False)
                            reachable |= {i}
                            reachable = close_forward(reachable) # just in case
                            break
                    if not initial:
                        continue
                    # now, check if r /\ ps /\ q |= wp(r /\ ps -> q)
                    _cti: Optional[Tuple[PDState, PDState]]
                    _ps: Optional[Tuple[Predicate,...]]
                    if False:
                        # version using cti_solver
                        p_seed = frozenset(range(len(ps)))
                        _cti = check_q(q_seed, p_seed,  utils.args.optimize_ctis)
                        if _cti is None:
                            print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: dual edge is valid, minimizing ps')
                            for i in sorted(p_seed, reverse=True):
                                if check_q(q_seed, p_seed - {i}, False) is None:
                                    p_seed -= {i}
                            print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: done minimizing ps')
                            _ps = tuple(ps[i] for i in sorted(p_seed))
                        else:
                            _ps = None
                        if False:
                            # just check vs. check_dual_edge
                            # TODO: run this on all examples sometime
                            if _cti is None:
                                assert _ps is not None
                                assert check_dual_edge(
                                    solver,
                                    _ps,
                                    tuple(q),
                                    msg='validation-cti'
                                ) == (_cti, _ps)
                            else:
                                assert check_dual_edge(
                                    solver,
                                    tuple(ps),
                                    tuple(q),
                                    msg='validation-cti'
                                )[0] is not None
                    elif True:
                        # version using check_dual_edge_optimize
                        _cti, _ps = check_dual_edge_optimize(
                            tuple(ps),
                            mp.top_clauses,
                            tuple(q_seed),
                        )
                    else:
                        # version using check_dual_edge
                        _cti, _ps = check_dual_edge(
                            solver,
                            tuple(ps),
                            tuple(q),
                            # msg='cti?', TODO
                        )
                    if _cti is None:
                        assert _ps is not None
                        _qs = tuple(q)
                        print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: n_literals={n_literals}, n_ctis={n_ctis}, found=True, learned {len(internal_ctis) - n_internal_ctis} new internal ctis and {len(reachable) - n_reachable} new reachable states')
                        print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: found new dual edge ({len(_ps)} predicates --> {len(_qs)} predicates):')
                        for p in _ps:
                            print(f'  {p}')
                        print('  --> ')
                        for qq in _qs:
                            print(f'  {qq}')
                        print(f'[{datetime.now()}] find_dual_edge: done')
                        return _ps, _qs
                    else:
                        prestate, poststate = _cti
                        i_pre = add_state(prestate, True)
                        i_post = add_state(poststate, True)
                        #production# assert (i_pre, i_post) not in transitions
                        add_transition(i_pre, i_post)
                        ctis |= {i_pre, i_post}
                        find_dual_edge_ctis[goals] |= {i_pre, i_post}
                        n_ctis += 1
                        print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: found new cti')
                # here, we have enough internal_ctis to rule out all possible q's
                assert check_sep(ctis) is None, (ctis, check_sep(ctis))
                added_new_p = False
                if n_ps is None:
                    # minimize ctis outside of pos and learn a new predicate that separates them from pos
                    # TODO: use unsat cores to speed this up
                    # soft_neg = ctis - pos
                    for i in sorted(ctis - pos):
                       if i in ctis and check_sep(ctis - {i}) is None:
                           ctis -= {i}
                    assert check_sep(ctis) is None, (ctis, check_sep(ctis))
                    to_eliminate = ctis - pos
                    print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: looking for a new p that will eliminate some of: {sorted(to_eliminate)}')
                    for i in sorted(to_eliminate):
                        while True:
                            seed = maps[i].separate(
                                (size,),
                                permanent_pos=sorted(reachable),
                                pos=sorted(pos),
                                neg=[i],
                                pos_ps=[0],
                                # soft_neg=soft_neg, # TODO: or to_eliminate ?
                            )
                            if seed is None:
                                break
                            p = maps[i].to_clause(0, seed[0])
                            print(f'PID={os.getpid()} [{datetime.now()}] find_dual_edge: potential p is: {p}')
                            s = check_initial(solver, p)
                            if s is None:
                                break
                            else:
                                assert False # TODO: remove all this to simplify the code
                                print(f'  this predicate is not initial, learned a new initial state')
                                reachable |= {add_state(s, False)}
                                reachable = close_forward(reachable) # just in case
                        if seed is not None:
                            add_p(p)
                            added_new_p = True
                            print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: found new p predicate: {p}')
                            break
                if added_new_p:
                    continue
                print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: cannot find any new p predicate')
                if size < max_size:
                    print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: cannot find dual edge upto size {size}, increasing size')
                    size += 1
                    continue
                print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: size limit reached')
                # we have not added a new p
                if len(goals) == n_qs:
                    print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: cannot find dual edge for this worklist item')
                    break
                # minimize ctis (including ones in pos) and add more worklist items
                # TODO: use unsat cores
                # TODO: do compute roots of some kind
                for i in sorted(ctis):
                   if i in ctis and check_sep(ctis - {i}) is None:
                       ctis -= {i}
                #production# assert check_sep(ctis) is None
                #production# assert len(ctis & reachable) == 0, sorted(ctis & reachable)
                if len(ctis) == 0:
                    print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: seems we learned the current goals are violated by reachable states, we have no ctis')
                else:
                    ctis = frozenset(i for i in ctis if maps[i].to_clause(0, maps[i].all_n[0]) not in goals)
                    print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: adding more worklist items to eliminate one of: {sorted(ctis)}')
                    for i in sorted(ctis):
                        g = maps[i].to_clause(0, maps[i].all_n[0])
                        #production# assert g not in goals
                        stateof[g] = i
                        new_goals = goals + (g,)
                        worklist.append(new_goals)
                break
        print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: n_literals={n_literals}, n_ctis={n_ctis}, found=False, learned {len(internal_ctis) - n_internal_ctis} new internal ctis and {len(reachable) - n_reachable} new reachable states')
        if len(worklist) == 0:
            print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: no more worklist items, so cannot find dual edge')
        else:
            print(f'[{datetime.now()}] [PID={os.getpid()}] find_dual_edge: ran out of worklist budget, reached induction width of {len(worklist[0]) - 1}')
        print(f'[{datetime.now()}] find_dual_edge: done')
        return None

    def find_dual_backward_transition(
            pos: Collection[int], # indices into states that ps must satisfy
            r: Collection[int], # indices into predicates that can be used (assumed invariants)
            goals: Collection[int], # indices into predicates that we want to find an edge to a subset of
    ) -> Optional[Tuple[Tuple[Predicate,...], Tuple[Predicate,...]]]:
        '''
        returns None or (ps, qs)
        no restriction on number of ps, the qs will be a subset of goals
        May add new reachable states if it finds new initial states
        '''
        print(f'[{datetime.now()}] find_dual_backward_transition: starting')
        nonlocal reachable
        pos = frozenset(pos)
        n_internal_ctis = len(internal_ctis)
        n_reachable = len(reachable)
        ps: List[Predicate] = [] # will be increasing
        goals = sorted(goals)
        qs = tuple(predicates[j] for j in goals)
        print(f'[{datetime.now()}] find_dual_backward_transition: starting, pos=states{sorted(pos)}, r=predicates{sorted(r)}, goals=predicates{goals}')
        n = len(qs)
        all_n = frozenset(range(n))
        #production# assert n > 0
        #production# assert cheap_check_implication(inits, qs)
        def find_fixpoint(s: Collection[int]) -> FrozenSet[int]:
            # a mini separation procedure for conjunction of qs
            imp = sorted((i, j) for i, j in chain(transitions, substructure) if i in s and j in s)
            x = frozenset(k for k in range(n) if all(eval_in_state(None, states[i], qs[k]) for i in sorted(reachable)))
            changes = True
            while changes:
                changes = False
                for i, j in imp:
                    if (    all(eval_in_state(None, states[i], qs[k]) for k in x) and
                        not all(eval_in_state(None, states[j], qs[k]) for k in x)):
                        x = frozenset(k for k in x if eval_in_state(None, states[j], qs[k]))
                        changes = True
            return x
        cti_solver = Solver() # TODO: maybe solver per transition
        t = cti_solver.get_translator(2)
        q_indicators_pre = tuple(z3.Bool(f'@q_pre_{i}') for i in range(n)) # NB: polarity
        q_indicators_post = tuple(z3.Bool(f'@q_post_{i}') for i in range(n)) # NB: polarity
        # there is some craziness here about mixing a mypyvy clause with z3 indicator variables
        # add the cube defined by q_indicators_pre to the prestate
        for indicator, q in zip(q_indicators_pre, qs):
            cti_solver.add(z3.Implies(indicator, t.translate_expr(q))) # NB: polarity
        # each q_indicator implies q has to be violated in the poststate
        for indicator, q in zip(q_indicators_post, qs):
            cti_solver.add(z3.Implies(indicator, z3.Not(t.translate_expr(New(q))))) # NB: polarity
        # add transition indicators
        transition_indicators: List[z3.ExprRef] = []
        for i, trans in enumerate(prog.transitions()):
            transition_indicators.append(z3.Bool(f'@transition_{i}_{trans.name}'))
            cti_solver.add(z3.Implies(transition_indicators[i], t.translate_expr(trans.as_twostate_formula(prog.scope))))
        p_indicators: List[z3.ExprRef] = []
        def add_p(p: Predicate) -> None:
            assert len(p_indicators) == len(ps)
            i = len(ps)
            ps.append(p)
            p_indicators.append(z3.Bool(f'@p_{i}'))
            cti_solver.add(z3.Implies(p_indicators[i], t.translate_expr(p)))
            cti_solver.add(z3.Implies(p_indicators[i], t.translate_expr(New(p))))
        def check_qs(qs_seed: FrozenSet[int], ps_seed: FrozenSet[int], optimize: bool = True) -> Optional[Tuple[PDState, PDState]]:
            for q_post_i, transition_indicator in product(sorted(qs_seed), transition_indicators):
                q_indicator = q_indicators_post[q_post_i]
                print(f'[{datetime.now()}] check_qs (find_dual_backward_transition): testing {q_indicator}, {transition_indicator}')
                indicators = tuple(chain(
                    [q_indicator, transition_indicator],
                    (q_indicators_pre[i] for i in sorted(qs_seed)),
                    (p_indicators[i] for i in sorted(ps_seed)),
                ))
                z3res = cti_solver.check(indicators)
                assert z3res in (z3.sat, z3.unsat)
                print(f'[{datetime.now()}] check_qs (find_dual_backward_transition): {z3res}')
                if z3res == z3.unsat:
                    continue
                if optimize:
                    # maximize indicators, to make for a more informative cti
                    for extra in chain(
                            # priorities: post, pre, ps
                            (q_indicators_post[i] for i in range(n) if i != q_post_i),
                            (q_indicators_pre[i] for i in sorted(all_n - qs_seed)),
                            (p_indicators[i] for i in range(len(p_indicators)) if i not in ps_seed),
                    ):
                        z3res = cti_solver.check(indicators + (extra,))
                        assert z3res in (z3.sat, z3.unsat)
                        if z3res == z3.sat:
                            print(f'[{datetime.now()}] check_qs (find_dual_backward_transition): adding extra: {extra}')
                            indicators += (extra,)
                    z3res = cti_solver.check(indicators) # note, this check is important, not just an assertion
                    assert z3res == z3.sat
                prestate, poststate = unpack_cti(cti_solver.model(indicators))
                print(f'[{datetime.now()}] check_qs: found new cti violating dual edge')
                _cache_transitions.append((prestate, poststate))
                for state in (prestate, poststate):
                    if all(eval_in_state(None, state, p) for p in inits):
                        _cache_initial.append(state)
                return prestate, poststate
            return None
        for j in sorted(r):
            add_p(predicates[j])
        while True:
            while True: # find potential qs or discover there are none and learn internal_ctis
                ctis = frozenset(
                    i for i in sorted((live_states | internal_ctis) - reachable)
                    if all(eval_in_state(None, states[i], p) for p in ps)
                )
                qs_seed = find_fixpoint(ctis)
                if len(qs_seed) == 0:
                    break
                print(f'[{datetime.now()}] find_dual_backward_transition: potential qs are ({len(qs_seed)}): predicates{sorted(goals[i] for i in qs_seed)}')
                # now, check if r /\ ps /\ qs_seed |= wp(r /\ ps -> qs_seed)
                _cti: Optional[Tuple[PDState, PDState]]
                _ps: Optional[Tuple[Predicate,...]]
                if False:
                    # version using cti_solver
                    p_seed = frozenset(range(len(ps)))
                    _cti = check_qs(qs_seed, p_seed, utils.args.optimize_ctis)
                    if _cti is None:
                        print(f'[{datetime.now()}] find_dual_backward_transition: dual edge is valid, minimizing ps')
                        for i in sorted(p_seed, reverse=True):
                            if check_qs(qs_seed, p_seed - {i}, False) is None:
                                p_seed -= {i}
                        print(f'[{datetime.now()}] find_dual_backward_transition: done minimizing ps')
                        _ps = tuple(ps[i] for i in sorted(p_seed))
                    else:
                        _ps = None
                else:
                    mp = MultiSubclausesMapICE(tuple(qs[i] for i in sorted(qs_seed)), [], []) # only used to compute q_seed
                    q_seed = tuple(
                        frozenset(range(mp.n[k]))
                        for k in range(mp.m)
                    )
                    _cti, _ps = check_dual_edge_optimize(
                        tuple(ps),
                        mp.top_clauses,
                        q_seed,
                        whole_clauses=True,
                    )
                if False:
                    # just check result vs. check_dual_edge
                    # TODO: run this on all examples sometime
                    if _cti is None:
                        assert _ps is not None
                        assert check_dual_edge(
                            solver,
                            _ps,
                            tuple(qs[i] for i in sorted(qs_seed)),
                            msg='validation-cti'
                        ) == (_cti, _ps)
                    else:
                        assert check_dual_edge(
                            solver,
                            tuple(ps),
                            tuple(qs[i] for i in sorted(qs_seed)),
                            msg='validation-cti'
                        )[0] is not None
                if _cti is None:
                    assert _ps is not None
                    _qs = tuple(qs[i] for i in sorted(qs_seed))
                    print(f'[{datetime.now()}] find_dual_backward_transition: learned {len(internal_ctis) - n_internal_ctis} new internal ctis and {len(reachable) - n_reachable} new reachable states')
                    print(f'[{datetime.now()}] find_dual_backward_transition: found new dual edge ({len(_ps)} predicates --> {len(_qs)} predicates):')
                    for p in _ps:
                        print(f'  {p}')
                    print(f'  -->')
                    for q in _qs:
                        print(f'  {q}')
                    print(f'[{datetime.now()}] find_dual_backward_transition: done')
                    return _ps, _qs
                else:
                    prestate, poststate = _cti
                    i_pre = add_state(prestate, True)
                    i_post = add_state(poststate, True)
                    #production# assert (i_pre, i_post) not in transitions
                    add_transition(i_pre, i_post)
            # here, we have enough internal_ctis to rule out all nonempty subsets of qs
            #production# assert len(find_fixpoint(ctis)) == 0
            # minimize ctis outside of pos and learn a new predicate that separates them from pos
            # TODO: use unsat cores
            soft_neg = ctis - pos
            for i in sorted(ctis - pos):
               # if i in ctis and len(find_fixpoint(ctis - {i})) == 0 is None:  # TODO(jrw): this line makes no sense; it compares `0 is None` to an int...
               # oded: I fixed it, but haven't tested it and it seems before this if was never taken, so it may be buggy
               if i in ctis and len(find_fixpoint(ctis - {i})) == 0:  # TODO(jrw): this line makes no sense; it compares `0 is None` to an int...
                   ctis -= {i}
            #production# assert len(find_fixpoint(ctis)) == 0
            to_eliminate = ctis - pos
            print(f'[{datetime.now()}] find_dual_backward_transition: looking for a new p that will eliminate some of: {sorted(to_eliminate)}')
            for i in sorted(to_eliminate):
                while True:
                    seed = maps[i].separate(
                        (max_size,), # TODO: iterate over sizes
                        permanent_pos=sorted(reachable),
                        pos=sorted(pos),
                        neg=[i],
                        pos_ps=[0],
                        # soft_neg=soft_neg, # TODO: or to_eliminate ?
                    )
                    if seed is None:
                        break
                    p = maps[i].to_clause(0, seed[0])
                    print(f'[{datetime.now()}] find_dual_backward_transition: potential p is: {p}')
                    s = check_initial(solver, p)
                    if s is None:
                        break
                    else:
                        assert False # TODO: remove all this to simplify the code
                        print(f'  this predicate is not initial, learned a new initial state')
                        reachable |= {add_state(s, False)}
                        reachable = close_forward(reachable) # just in case
                if seed is not None:
                    add_p(p)
                    print(f'[{datetime.now()}] find_dual_backward_transition: found new p predicate: {p}')
                    break
            else:
                print(f'[{datetime.now()}] find_dual_backward_transition: learned {len(internal_ctis) - n_internal_ctis} new internal ctis and {len(reachable) - n_reachable} new reachable states')
                print(f'[{datetime.now()}] find_dual_backward_transition: cannot find any new p predicate, so cannot find dual edge')
                print(f'[{datetime.now()}] find_dual_backward_transition: done')
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
        return #TODO# #production#
        assert reachable == close_forward(reachable), sorted(close_forward(reachable) - reachable)
        #TODO# assert reachable == close_forward(reachable, True), sorted(close_forward(reachable, True) - reachable) # TODO: not sure about this, see paxos_forall.pd-primal-dual-houdini.dfc198b.log, paxos_forall.pd-primal-dual-houdini.5e0ed39.log
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

    def print_status_and_check_termination() -> Optional[str]:
        nonlocal human_invariant_proved
        # print status
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
        print(f'\n[{datetime.now()}] Current transitions ({len(transitions)}) and substructures ({len(substructure)}):')
        for i, j, label in sorted(chain(
                ((i, j, 'transition') for i, j in transitions),
                ((i, j, 'substructure') for i, j in substructure),
        )):
            print(f'  {i:3} -> {j:3} ({label})')
        print(f'\n[{datetime.now()}] Current predicates ({len(live_predicates)} total, {len(inductive_invariant)} proven, {len(live_predicates & human_invariant_implies)} implied by human invariant):')
        for i in sorted(live_predicates):
            max_frame = max((j for j, f in enumerate(frames) if predicates[i] in f), default=-1)
            #production# assert max_frame < len(frames) - 1 or i in inductive_invariant
            note = (' (invariant)' if i in inductive_invariant else f' ({max_frame + 1})')
            max_frame = max((j for j, f in enumerate(step_frames) if predicates[i] in f), default=-1)
            #production# assert max_frame < len(step_frames) - 1 or i in inductive_invariant
            if i not in inductive_invariant:
                note += f' ({max_frame + 1})'
            if i in human_invariant_implies:
                note += f' (implied by human invariant)'
            print(f'  predicates[{i:3}]{note}: {predicates[i]}')
        print(f'\n[{datetime.now()}] Current dual transitions ({len(dual_transitions)}):')
        for ii, jj in dual_transitions:
            print(f'  {sorted(ii)} -> {sorted(jj)}')
        print()
        for i, p in enumerate(human_invariant):
            if i not in human_invariant_proved and len(inductive_invariant) > 0 and cheap_check_implication([predicates[j] for j in sorted(inductive_invariant)], [p]):
                human_invariant_proved.add(i)
        print(f'\n[{datetime.now()}] Current human invariant ({len(human_invariant)} total, {len(human_invariant_to_predicate)} learned, {len(human_invariant_proved)} proven):')
        for i, p in enumerate(human_invariant):
            notes = []
            if i in human_invariant_proved:
                notes.append('proved')
            if i in human_invariant_to_predicate:
                notes.append(f'learned as predicates[{human_invariant_to_predicate[i]}]')
            note = '(' + ', '.join(notes) + ')'
            print(f'  human_invariant[{i:3}]{note}: {p}')
        print()
        # check termination condition
        if len(inductive_invariant) > 0 and cheap_check_implication([predicates[i] for i in sorted(inductive_invariant)], safety):
            print(f'[{datetime.now()}] Proved safety!')
            return 'SAFE'
        for i in reachable:
            if not cheap_check_implication([states[i].as_onestate_formula(0)], safety):
                print(f'\n[{datetime.now()}] Found safety violation by reachable state (states[{i}]).')
                return 'UNSAFE'
        return None

    if hasattr(utils.args, 'restart_from') and utils.args.restart_from is not None:
        restart_from_file(utils.args.restart_from)

    first_iteration = True
    while True:
        # TODO: add a little BMC
        assert_invariants()

        print(f'[{datetime.now()}] New global iteration')

        if not first_iteration:
            save_algorithm_state()
        else:
            first_iteration = False

        n_inductive_invariant = len(inductive_invariant)
        n_reachable = len(reachable)
        houdini_frames()
        compute_step_frames()
        if len(reachable) > n_reachable:
            print(f'[{datetime.now()}] Primal Houdini found {len(reachable) - n_reachable} new reachable states')
            new_reachable_states()
        if len(inductive_invariant) > n_inductive_invariant:
            print(f'[{datetime.now()}] Primal Houdini found {len(inductive_invariant) - n_inductive_invariant} new inductive predicates')
            new_inductive_invariants()

        assert_invariants()

        # print status and possibly terminate
        result = print_status_and_check_termination()
        if result is not None:
            dump_caches()
            return result

        # # if we learned a new inductive invariant or reachable state, "restart"
        # if len(inductive_invariant) > n_inductive_invariant or len(reachable) > n_reachable:
        #     print(f'[{datetime.now()}] Restarting due to new reachble or inductive, cleaning up all non-reachable states')
        #     # live_predicates = frozenset(
        #     #     j for j in sorted(live_predicates)
        #     #     if j in inductive_invariant or predicates[j] in safety
        #     # )
        #     live_states = reachable
        #     continue

        n_predicates = len(predicates)
        n_live_predicates = len(live_predicates)
        n_inductive_invariant = len(inductive_invariant)
        n_reachable = len(reachable)
        n_live_states = len(live_states)
        n_internal_ctis = len(internal_ctis)
        dual_houdini_frames()
        #production# assert reachable == close_forward(reachable)
        #production# assert inductive_invariant == dual_close_forward(inductive_invariant)
        if len(reachable) > n_reachable:
            print(f'[{datetime.now()}] Dual Houdini found {len(reachable) - n_reachable} new reachable states')
            new_reachable_states()
        if len(inductive_invariant) > n_inductive_invariant:
            print(f'[{datetime.now()}] Dual Houdini found {len(inductive_invariant) - n_inductive_invariant} new inductive predicates')
            new_inductive_invariants()
        assert_invariants()
        print(f'\n[{datetime.now()}] After Dual Houdini: learned {len(predicates) - n_predicates} new predicates,'
              f'revived {len(live_predicates) - n_live_predicates - len(predicates) + n_predicates} previous predicates,'
              f'learned {len(inductive_invariant) - n_inductive_invariant} new inductive predicates, ',
              f'{len(reachable) - n_reachable} new reachable states,'
              f'{len(live_states) - n_live_states} new live states, '
              f'{len(internal_ctis) - n_internal_ctis} new internal ctis, '
              f'looping\n')

        # print status and possibly terminate
        result = print_status_and_check_termination()
        if result is not None:
            dump_caches()
            return result

        # # if we learned a new inductive invariant or reachable state, "restart"
        # if len(inductive_invariant) > n_inductive_invariant or len(reachable) > n_reachable:
        #     print(f'[{datetime.now()}] Restarting due to new reachble or inductive, cleaning up all non-reachable states')
        #     # live_predicates = frozenset(
        #     #     j for j in sorted(live_predicates)
        #     #     if j in inductive_invariant or predicates[j] in safety
        #     # )
        #     live_states = reachable
        #     continue

        if not any([
            # TODO: think about this condition better
            n_predicates != len(predicates),
            n_live_predicates != len(live_predicates),
            n_inductive_invariant != len(inductive_invariant),
            # n_reachable != len(reachable),
            # n_live_states != len(live_states),
            # n_internal_ctis != len(internal_ctis),
        ]):
            print(f'[{datetime.now()}] Fixed point of induction width reached without a safety proof!')
            dump_caches()
            return 'UNPROVABLE'

# class DualEdgeFinder:
#     '''Class used to store a map of subclauses of several clauses, and
#     obtain a conjunction of subclauses that satisfy positive,
#     negative, and implication constraints on some given states.
#     '''
#     def __init__(self,
#                  states: List[PDState],  # assumed to only grow
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
#         free = set(chain(*(free_ids(lit) for lit in lits)))
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
class MonotoneFunction:
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
# def separate(solver: Solver, A: Sequence[PDState], B: Sequence[PDState], k: int) -> Optional[Sequence[Predicate]]:
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
#         cs = as_clauses(Not(Diagram(s.as_state(0)).to_ast()))
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
#                    states: Sequence[PDState],
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

#     states : List[PDState] = []
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


def minimize_clause(p: Expr, states: Sequence[PDState]) -> Expr:
    '''
    p is a clause, try to find a smaller clause satisfied by all states
    '''
    if p == FalseExpr:
        return p
    variables, literals = destruct_clause(p)
    n = len(literals)

    def to_clause(s: Set[int]) -> Expr:
        lits = [literals[i] for i in s]
        free = set(chain(*(free_ids(lit) for lit in lits)))
        vs = tuple(v for v in variables if v.name in free)
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
# class SeparabilitySubclausesMap:
#     '''
#     Class used to store a map of subclauses of a certain clause, and
#     obtain subclauses that are positive and negative on some given
#     states.
#     '''
#     def __init__(self,
#                  top_clause: Expr,
#                  states: List[PDState],  # assumed to only grow
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
#         free = set(chain(*(free_ids(lit) for lit in lits)))
#         vs = [v for v in self.variables if v.name in free]
#         return Forall(vs, Or(*lits)) if len(vs) > 0 else Or(*lits)


class SeparabilityMap:
    '''
    Marco map for function sep: 2^states x 2^states -> {0,1}
    0 means they can be separated, 1 means they cannot.
    '''
    def __init__(self,
                 states: List[PDState],  # assumed to only grow
                 predicates: List[Expr],  # assumed to only grow
    ):
        self.states = states
        self.predicates = predicates
        self.maps: List[SubclausesMapTurbo] = []
        self._new_states()

    def _new_states(self) -> None:
        # create new SubclausesMapTurbo's
        for i in range(len(self.maps), len(self.states)):
            cs = as_clauses(Not(Diagram(self.states[i].as_state(0)).to_ast()))
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
    def safe(s: PDState) -> bool:
        return all(eval_in_state(solver, s, p) for p in safety)

    states : List[PDState] = []
    reachable: List[int] = []
    backward_reachable: List[int] = []
    transitions: List[Tuple[int, int]] = []
    # paths: List[Tuple[int, int]] = []

    def add_state(s: PDState) -> int:
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

    def alpha_sharp(states: Collection[PDState]) -> Sequence[Expr]:
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
        def alpha_a(states: Collection[PDState]) -> Sequence[Expr]:
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
                if isinstance(p, tuple):
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
# class PrimalDualBoundsAlgorithm:
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
#         self.states : List[PDState] = []
#         self.predicates : List[Predicate] = list(chain(*(as_clauses(x) for x in self.safety)))
#         # TODO: we are not taking sharp subclauses of safety, maybe to get
#         # the same effect we can take the powerset (safety is usually not
#         # so many literals)
#
#         self.reachable_states: Set[PDState] = set()  # subset of states
#         self.invariant_predicates: Set[Predicate]  # subset of predicates
#
#         """
#         self.transition_state: Dict[Tuple[PDState, PDState], bool] = dict()  # partial function, is there a transition or not, or maybe we don't know yet
#         self.transition_predicate: Dict[Tuple[FrozenSet[Predicate],PDState,Predicate], bool] = dict()  # monotone, needs symbolic representation
#         self.path: Dict[Tuple[PDState, PDState], bool] = dict()
#         self.hoare:  Dict[Tuple[FrozenSet[Predicate], FrozenSet[Predicate], Predicate], bool] = dict() # monotone partial function, TODO: should be stored differently
#         self.induction: Dict[Tuple[FrozenSet[PDState], FrozenSet[Predicate], Predicate], bool] = dict() # anti-monotone in states, monotone in predicates, TODO: should be stored differently
#         self.inseperable: Dict[Tuple[FrozenSet[PDState], FrozenSet[PDState]], Optional[int]] = dict() # monotone Nat_inf (None represents inf), TODO: should be stored differently
#         assert not self.sharp #  TODO: inseprable does not support sharp, should be made Dict[Tuple[FrozenSet[PDState], FrozenSet[PDState], FrozenSet[PDState]], Optional[int]]
#         # TODO: bounds
#         """
#
#         # version with BMC in mind:
#         NatInf = Optional(int) # None represents infinity, -k represents that the object whose size we are trying to bound actually exists with size k
#         self.transition_state: Dict[Tuple[FrozenSet[Predicate], PDState, PDState], NatInf] = defaultdict(int) # lower bound (from BMC) on trace from state to state, all satisfying P
#         self.transition_predicate: Dict[Tuple[FrozenSet[Predicate],PDState,Predicate], NatInf] = defaultdict(int)  # as above, but for predicate
#
#         self.path: Dict[Tuple[PDState, PDState], bool] = dict()
#         self.hoare:  Dict[Tuple[FrozenSet[Predicate], FrozenSet[Predicate], Predicate], bool] = dict() # monotone partial function, TODO: should be stored differently
#         self.induction: Dict[Tuple[FrozenSet[PDState], FrozenSet[Predicate], Predicate], bool] = dict() # anti-monotone in states, monotone in predicates, TODO: should be stored differently
#         self.inseperable: Dict[Tuple[FrozenSet[PDState], FrozenSet[PDState]], Optional[int]] = dict() # monotone Nat_inf (None represents inf), TODO: should be stored differently
#         assert not self.sharp #  TODO: inseprable does not support sharp, should be made Dict[Tuple[FrozenSet[PDState], FrozenSet[PDState], FrozenSet[PDState]], Optional[int]]
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
#     def check_transition_state_state(self, s: PDState, t: PDState) -> None:
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
#             prestate = Trace.from_z3((KEY_OLD,), z3m)
#             poststate = Trace.from_z3([KEY_NEW, KEY_OLD], z3m)
#             assert isomorphic_states(self.solver, s, prestate)
#             assert isomorphic_states(self.solver, t, poststate)
#
#     def check_transition_state_predicate(self, G: Sequence[Predicate], s: PDState, q: Predicate) -> None:
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
    states: List[Trace] = []
    t1 = s.get_translator(1)
    t2 = s.get_translator(2)
    with s.new_frame():
        for sort in prog.sorts():
            b = 2
            # an old hack for paxos that is commented out below
            # if sort.name == 'round':
            #     b = 3
            # else:
            #     b = 2
            print(f'bounding {sort} to candinality {b}')
            s.add(s._sort_cardinality_constraint(Z3Translator.sort_to_z3(sort), b))

        unknown = False

        def block_state(t: Z3Translator, m: Trace) -> None:
            # TODO: with the diagram, smaller states block larger
            # ones, but with onestate it's slower (paxos can't get
            # beyond initial states with 2 of everything). we should
            # collect states by the sizes of their universe

            s.add(t.translate_expr(New(Not(m.as_onestate_formula(0)), t.num_states - 1)))

        print('looking for initial states')
        with s.new_frame():
            for init in prog.inits():
                s.add(t1.translate_expr(init.expr))
            while True:
                print(f'{len(states)} total states so far')
                res = s.check()
                if res == z3.unsat:
                    break
                elif res == z3.unknown:
                    unknown = True
                    break
                else:
                    m = Z3Translator.model_to_trace(s.model(minimize=False), 1)
                    states.append(m)
                    block_state(t1, m)
        print(f'done finding initial states! found {len(states)} states')

        print('looking for transitions to new states')
        with s.new_frame():
            for state in states:
                block_state(t2, m)

            worklist = list(product(states, prog.transitions()))
            while len(worklist) > 0:
                print(f'worklist has length {len(worklist)}')
                state, ition = worklist.pop()
                new_states = []
                with s.new_frame():
                    s.add(t2.translate_expr(state.as_onestate_formula(0)))
                    s.add(t2.translate_expr(ition.as_twostate_formula(prog.scope)))
                    while True:
                        res = s.check()
                        if res == z3.unsat:
                            break
                        elif res == z3.unknown:
                            unknown = True
                            break
                        _, m = unpack_cti(s.model(minimize=False), keep_prestate_in_poststate=True)
                        new_states.append(m)
                        block_state(t2, m)
                for state in new_states:
                    worklist.extend([(state, x) for x in prog.transitions()])
                    block_state(t2, m)
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


def incremental_induction_graph(solver: Solver) -> str:
    '''
    Compute incremental induction graph of human invariant
    '''
    prog = syntax.the_program
    print(f'\n[{datetime.now()}] [PID={os.getpid()}] Starting incremental_induction_graph\n')

    predicates = tuple(chain(*(as_clauses(inv.expr) for inv in prog.invs()))) # convert to CNF
    dual_transitions: List[Tuple[FrozenSet[int], FrozenSet[int]]] = []
    proven: Set[int] = set()
    unproven = set(range(len(predicates)))

    print(f'\n[{datetime.now()}] Predicates from human invariant ({len(predicates)}):')
    for i, p in enumerate(predicates):
        print(f'  [{i:3}]: {p}')

    check_dual_edge_cache: Dict[Tuple[FrozenSet[int], FrozenSet[int]], bool] = dict()
    def get_from_cache(ps: FrozenSet[int], qs: FrozenSet[int]) -> Optional[bool]:
        if (ps, qs) in check_dual_edge_cache:
            return check_dual_edge_cache[ps, qs]
        for (ps_, qs_), v in check_dual_edge_cache.items():
            if qs == qs_:
                if (not v) and ps <= ps_:
                    return False
                elif v and ps >= ps_:
                    return True
        return None
    def check_dual_edge(ps: FrozenSet[int], qs: FrozenSet[int]) -> bool:
        def check(ps: FrozenSet[int], qs: FrozenSet[int]) -> bool:
            if get_from_cache(ps, qs) is None:
                print(f'[{datetime.now()}]  Checking edge:')
                for j in sorted(ps):
                    print(f'  {predicates[j]}')
                print('  --> ')
                for j in sorted(qs):
                    print(f'  {predicates[j]}')
                if False:
                    # doesn't use CVC4
                    cti, _ps = check_dual_edge(
                        solver,
                        tuple(predicates[j] for j in sorted(ps)),
                        tuple(predicates[j] for j in sorted(qs)),
                    )
                else:
                    # uses CVC4
                    cti = check_dual_edge_optimize_find_cti(
                        tuple(predicates[j] for j in sorted(ps)),
                        tuple(predicates[j] for j in sorted(qs)),
                        tuple(frozenset(range(len(destruct_clause(predicates[j])[1]))) for j in sorted(qs)),
                        True,
                    )
                if cti is None:
                    print(f'[{datetime.now()}]  Valid!')
                else:
                    print(f'[{datetime.now()}]  Invalid!')
                check_dual_edge_cache[ps, qs] = cti is None
            v = get_from_cache(ps, qs)
            assert v is not None
            return v

        if get_from_cache(ps, qs) is None:
            if check(ps, qs):
               assert get_from_cache(ps, qs) is True
            else:
                # try to add more predicates to ps, and obtain a maximal ps such
                for j in range(len(predicates)):
                    if j not in ps and not check(ps | {j}, qs):
                        ps |= {j}
                # now ps is maximal, add all subsets of ps to cache
                print(f'[{datetime.now()}]  Found maximal invalid edge:')
                for j in sorted(ps):
                    print(f'  {predicates[j]}')
                print('  --> ')
                for j in sorted(qs):
                    print(f'  {predicates[j]}')
                print()
        v = get_from_cache(ps, qs)
        assert v is not None
        return v

    n_ps = 0
    n_qs = 1
    while len(proven) < len(predicates):
        edges = [(ps, qs) for (ps, qs) in
                 product(combinations(sorted(proven), n_ps), combinations(sorted(unproven), n_qs))
                 if get_from_cache(frozenset(ps), frozenset(qs)) is not False]
        print(f'\n[{datetime.now()}] Checking {n_ps} --> {n_qs} edges (total of {len(edges)}):')
        for i, (ps, qs) in enumerate(edges):
            print(f'[{datetime.now()}]  Checking edge {i:10}:')
            for j in ps:
                print(f'  {predicates[j]}')
            print('  --> ')
            for j in qs:
                print(f'  {predicates[j]}')
            print()
            if check_dual_edge(frozenset(ps), frozenset(qs)):
                print(f'[{datetime.now()}] found dual edge:')
                for j in ps:
                    print(f'  {predicates[j]}')
                print('  --> ')
                for j in qs:
                    print(f'  {predicates[j]}')
                dual_transitions.append((frozenset(ps), frozenset(qs)))
                proven |= set(qs)
                unproven -= set(qs)
                n_ps = 0
                n_qs = 1
                break
        else:
            # no new predicate was proven, increase n_ps if possible, otherwise increase n_qs
            print(f'\n[{datetime.now()}] No {n_ps} --> {n_qs} edges found')
            n_ps += 1
            if n_ps > len(proven):
                n_ps = 0
                n_qs += 1
                assert n_qs <= len(unproven)

    print(f'\n[{datetime.now()}] Dual edges found ({len(dual_transitions)}):')
    for ii, jj in dual_transitions:
        print(f'  {sorted(ii)} --> {sorted(jj)}')
    print()
    return ''


def test(solver: Solver) -> str:
    '''
    test map_clause_state_interaction_z3's performance
    '''
    prog = syntax.the_program
    print(f'\n[{datetime.now()}] [PID={os.getpid()}] test\n')

    top_clauses = (parse_and_typecheck_expr('forall node_0:node, node_1:node, node_2:node, node_3:node, quorum_c_0:quorum_c, quorum_c_1:quorum_c, quorum_c_2:quorum_c, quorum_f_0:quorum_f, round_0:round, round_1:round, round_2:round, round_3:round, value_0:value, value_1:value. node_0 = node_1 | node_0 = node_2 | node_0 = node_3 | node_1 = node_2 | node_1 = node_3 | node_2 = node_3 | quorum_c_0 = quorum_c_1 | quorum_c_0 = quorum_c_2 | quorum_c_1 = quorum_c_2 | round_0 = round_1 | round_0 = round_2 | round_0 = round_3 | round_1 = round_2 | round_1 = round_3 | round_2 = round_3 | value_0 = value_1 | fast(round_0) | !fast(round_1) | fast(round_2) | fast(round_3) | !le(round_0, round_0) | !le(round_0, round_1) | !le(round_0, round_2) | !le(round_0, round_3) | le(round_1, round_0) | !le(round_1, round_1) | !le(round_1, round_2) | !le(round_1, round_3) | le(round_2, round_0) | le(round_2, round_1) | !le(round_2, round_2) | !le(round_2, round_3) | le(round_3, round_0) | le(round_3, round_1) | le(round_3, round_2) | !le(round_3, round_3) | member_c(node_0, quorum_c_0) | !member_c(node_0, quorum_c_1) | !member_c(node_0, quorum_c_2) | !member_c(node_1, quorum_c_0) | !member_c(node_1, quorum_c_1) | member_c(node_1, quorum_c_2) | !member_c(node_2, quorum_c_0) | member_c(node_2, quorum_c_1) | !member_c(node_2, quorum_c_2) | member_c(node_3, quorum_c_0) | !member_c(node_3, quorum_c_1) | member_c(node_3, quorum_c_2) | !member_f(node_0, quorum_f_0) | !member_f(node_1, quorum_f_0) | !member_f(node_2, quorum_f_0) | !member_f(node_3, quorum_f_0) | any_msg(round_0) | any_msg(round_1) | any_msg(round_2) | any_msg(round_3) | choosable_c(round_0, value_0, quorum_c_0) | choosable_c(round_0, value_0, quorum_c_1) | choosable_c(round_0, value_0, quorum_c_2) | choosable_c(round_0, value_1, quorum_c_0) | choosable_c(round_0, value_1, quorum_c_1) | choosable_c(round_0, value_1, quorum_c_2) | choosable_c(round_1, value_0, quorum_c_0) | choosable_c(round_1, value_0, quorum_c_1) | !choosable_c(round_1, value_0, quorum_c_2) | choosable_c(round_1, value_1, quorum_c_0) | choosable_c(round_1, value_1, quorum_c_1) | !choosable_c(round_1, value_1, quorum_c_2) | choosable_c(round_2, value_0, quorum_c_0) | choosable_c(round_2, value_0, quorum_c_1) | !choosable_c(round_2, value_0, quorum_c_2) | choosable_c(round_2, value_1, quorum_c_0) | choosable_c(round_2, value_1, quorum_c_1) | !choosable_c(round_2, value_1, quorum_c_2) | !choosable_c(round_3, value_0, quorum_c_0) | !choosable_c(round_3, value_0, quorum_c_1) | !choosable_c(round_3, value_0, quorum_c_2) | !choosable_c(round_3, value_1, quorum_c_0) | !choosable_c(round_3, value_1, quorum_c_1) | !choosable_c(round_3, value_1, quorum_c_2) | choosable_f(round_0, value_0, quorum_f_0) | choosable_f(round_0, value_1, quorum_f_0) | choosable_f(round_1, value_0, quorum_f_0) | choosable_f(round_1, value_1, quorum_f_0) | choosable_f(round_2, value_0, quorum_f_0) | choosable_f(round_2, value_1, quorum_f_0) | !choosable_f(round_3, value_0, quorum_f_0) | !choosable_f(round_3, value_1, quorum_f_0) | decision(round_0, value_0) | decision(round_0, value_1) | decision(round_1, value_0) | decision(round_1, value_1) | decision(round_2, value_0) | decision(round_2, value_1) | decision(round_3, value_0) | decision(round_3, value_1) | !left_round(node_0, round_0) | left_round(node_0, round_1) | left_round(node_0, round_2) | left_round(node_0, round_3) | !left_round(node_1, round_0) | !left_round(node_1, round_1) | !left_round(node_1, round_2) | left_round(node_1, round_3) | !left_round(node_2, round_0) | left_round(node_2, round_1) | left_round(node_2, round_2) | left_round(node_2, round_3) | !left_round(node_3, round_0) | !left_round(node_3, round_1) | left_round(node_3, round_2) | left_round(node_3, round_3) | one_a(round_0) | !one_a(round_1) | one_a(round_2) | !one_a(round_3) | one_b(node_0, round_0) | one_b(node_0, round_1) | one_b(node_0, round_2) | one_b(node_0, round_3) | one_b(node_1, round_0) | !one_b(node_1, round_1) | one_b(node_1, round_2) | one_b(node_1, round_3) | one_b(node_2, round_0) | !one_b(node_2, round_1) | one_b(node_2, round_2) | one_b(node_2, round_3) | one_b(node_3, round_0) | one_b(node_3, round_1) | one_b(node_3, round_2) | one_b(node_3, round_3) | proposal(round_0, value_0) | proposal(round_0, value_1) | proposal(round_1, value_0) | proposal(round_1, value_1) | proposal(round_2, value_0) | proposal(round_2, value_1) | proposal(round_3, value_0) | proposal(round_3, value_1) | vote(node_0, round_0, value_0) | vote(node_0, round_0, value_1) | vote(node_0, round_1, value_0) | vote(node_0, round_1, value_1) | vote(node_0, round_2, value_0) | vote(node_0, round_2, value_1) | vote(node_0, round_3, value_0) | vote(node_0, round_3, value_1) | vote(node_1, round_0, value_0) | vote(node_1, round_0, value_1) | vote(node_1, round_1, value_0) | vote(node_1, round_1, value_1) | vote(node_1, round_2, value_0) | vote(node_1, round_2, value_1) | vote(node_1, round_3, value_0) | vote(node_1, round_3, value_1) | vote(node_2, round_0, value_0) | vote(node_2, round_0, value_1) | vote(node_2, round_1, value_0) | vote(node_2, round_1, value_1) | vote(node_2, round_2, value_0) | vote(node_2, round_2, value_1) | vote(node_2, round_3, value_0) | vote(node_2, round_3, value_1) | vote(node_3, round_0, value_0) | vote(node_3, round_0, value_1) | vote(node_3, round_1, value_0) | vote(node_3, round_1, value_1) | vote(node_3, round_2, value_0) | vote(node_3, round_2, value_1) | vote(node_3, round_3, value_0) | vote(node_3, round_3, value_1) | none != round_0 | decision_quorum_c(round_0, value_0) != quorum_c_1 | decision_quorum_c(round_0, value_1) != quorum_c_1 | decision_quorum_c(round_1, value_0) != quorum_c_1 | decision_quorum_c(round_1, value_1) != quorum_c_1 | decision_quorum_c(round_2, value_0) != quorum_c_1 | decision_quorum_c(round_2, value_1) != quorum_c_1 | decision_quorum_c(round_3, value_0) != quorum_c_1 | decision_quorum_c(round_3, value_1) != quorum_c_1 | decision_quorum_f(round_0, value_0) != quorum_f_0 | decision_quorum_f(round_0, value_1) != quorum_f_0 | decision_quorum_f(round_1, value_0) != quorum_f_0 | decision_quorum_f(round_1, value_1) != quorum_f_0 | decision_quorum_f(round_2, value_0) != quorum_f_0 | decision_quorum_f(round_2, value_1) != quorum_f_0 | decision_quorum_f(round_3, value_0) != quorum_f_0 | decision_quorum_f(round_3, value_1) != quorum_f_0', 1),)

    print(f'\n[{datetime.now()}] top_clauses ({len(top_clauses)}):')
    for i, x in enumerate(top_clauses):
        print(f'  [{i:3}]: {x}')
    print()

    ps = [parse_and_typecheck_expr(st, 1) for st in [
        'forall round0:round, value0:value. !decision(round0, value0) | none != round0',
        'forall node0:node, round0:round, value0:value. any_msg(round0) | proposal(round0, value0) | !vote(node0, round0, value0)',
        'forall node0:node, quorum_f0:quorum_f, round0:round, value1:value. !fast(round0) | !member_f(node0, quorum_f0) | !decision(round0, value1) | vote(node0, round0, value1) | decision_quorum_f(round0, value1) != quorum_f0',
        'forall round0:round. fast(round0) | !any_msg(round0)',
        'forall round_1:round, value_1:value. fast(round_1) | !decision(round_1, value_1) | proposal(round_1, value_1)',
        'forall round0:round, value0:value, value1:value. value0 = value1 | !proposal(round0, value0) | !proposal(round0, value1)',
        'forall node0:node, round0:round, value0:value, value1:value. value0 = value1 | !vote(node0, round0, value0) | !vote(node0, round0, value1)',
        'forall node_0:node, round_1:round. one_a(round_1) | !one_b(node_0, round_1)',
        'forall round2:round. !any_msg(round2) | one_a(round2)',
        'forall round0:round, value0:value. one_a(round0) | !proposal(round0, value0)',
        'forall node0:node, round1:round, round2:round. !le(round1, round2) | left_round(node0, round1) | !left_round(node0, round2)',
        'forall node0:node, quorum_c0:quorum_c, round0:round, value0:value. fast(round0) | !member_c(node0, quorum_c0) | !decision(round0, value0) | vote(node0, round0, value0) | decision_quorum_c(round0, value0) != quorum_c0',
        'forall round0:round. !one_a(round0) | none != round0',
        'forall node0:node, round0:round, round1:round. round0 = round1 | !le(round0, round1) | left_round(node0, round0) | !one_b(node0, round1)',
        'forall quorum_f_0:quorum_f, round_1:round, round_2:round, value_1:value. fast(round_1) | !le(round_1, round_2) | !choosable_f(round_1, value_1, quorum_f_0) | proposal(round_1, value_1) | !proposal(round_2, value_1)',
        'forall quorum_f0:quorum_f, round0:round, round1:round, value0:value. !le(round1, round0) | !any_msg(round0) | any_msg(round1) | !choosable_f(round1, value0, quorum_f0)',
    ]]

    print(f'\n[{datetime.now()}] ps ({len(ps)}):')
    for i, x in enumerate(ps):
        print(f'  [{i:3}]: {x}')
    print()


    qs = [parse_and_typecheck_expr('forall node_3:node, round_1:round. !fast(round_1) | !left_round(node_3, round_1) | !one_a(round_1) | one_b(node_3, round_1)', 1)]

    print(f'\n[{datetime.now()}] qs ({len(qs)}):')
    for i, x in enumerate(qs):
        print(f'  [{i:3}]: {x}')
    print()


    assert len(qs) == len(top_clauses)

    states: List[PDState] = []
    mp = MultiSubclausesMapICE(top_clauses, states, []) # only used to compute q_seed
    q_seed = [
        frozenset(j for j in range(mp.n[k]) if mp.literals[k][j] in destruct_clause(qs[k])[1])
        for k in range(mp.m)
    ]
    print(f'\n[{datetime.now()}] q_seed ({len(q_seed)}):')
    for i, y in enumerate(q_seed):
        print(f'  [{i:3}]: {y}')
    print()
    assert all(
        qs[k] == mp.to_clause(k, q_seed[k])
        for k in range(mp.m)
    )

    if False:
        # good test for check_dual_edge_optimize, took ~45 minutes, eventhough the original sat was received after a few seconds
        cti, _ = check_dual_edge_optimize(
            tuple(ps),
            mp.top_clauses,
            tuple(q_seed),
        )
    else:
        # use the optimal hq from the log file
        hq = HoareQuery(
            p=frozenset([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
            q_pre=(frozenset([109,113]),),
            q_post=(frozenset([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,122,123,124,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188]),),
            cardinalities=(),
            i_transition=0,
        )
        use_cvc4 = True
        timeout = 60
        q1 = CheckDualEdgeOptimizeJoinableQueue()
        q2 = CheckDualEdgeOptimizeQueue()
        args = (
            tuple(ps),
            top_clauses,
            hq,
            True, # produce_cti
            False, # optimize
            False, # whole_clauses
            use_cvc4,
            False,
            q1,
            q2,
            False, # join_q1
        )
        # assert_valid_hq(*args[:3])
        check_dual_edge_optimize_multiprocessing_helper(*args)
        hq2, valid, cti = q1.get(True)
        q1.task_done()
        assert hq == hq2
        assert not valid and cti is not None
    assert cti is not None
    prestate, poststate = cti
    print(f'\n[{datetime.now()}] prestate:\n{prestate}\n\n')
    states.append(prestate)
    print(f'[{datetime.now()}] Running mp._new_states([0])')
    mp._new_states([0])
    print(f'\n[{datetime.now()}] poststate:\n{poststate}\n\n')
    states.append(poststate)
    print(f'[{datetime.now()}] Running mp._new_states([1])')
    mp._new_states([1])
    print(f'[{datetime.now()}] Done!')
    return ''


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
    s.add_argument('--restart-from', help='.pd.gz filename to restart from')

    result.append(s)

    # incremental_induction_graph
    s = subparsers.add_parser('pd-incremental-induction-graph', help='Compute the incremental induction graph for the human invariant')
    s.set_defaults(main=incremental_induction_graph)
    result.append(s)

    # test
    s = subparsers.add_parser('pd-test', help='Used for various experiments and tests during development of pd.py code')
    s.set_defaults(main=test)
    result.append(s)

    for s in result:
        s.add_argument('--unroll-to-depth', type=int, help='Unroll transitions to given depth during exploration')
        s.add_argument('--cpus', type=int, help='Number of CPUs to use in parallel')
        s.add_argument('--restarts', action=utils.YesNoAction, default=False, help='Use restarts outside of Z3 by setting Luby timeouts')
        s.add_argument('--induction-width', type=int, default=1, help='Upper bound on weight of dual edges to explore.')
        s.add_argument('--all-subclauses',  action=utils.YesNoAction, default=False, help='Add all subclauses of predicates.')
        s.add_argument('--optimize-ctis',  action=utils.YesNoAction, default=True, help='Optimize internal ctis')
        s.add_argument('--domain-independence',  action=utils.YesNoAction, default=True, help='Restrict to domain independent clauses')
        s.add_argument('--max-quantifiers', type=int, help='Maximal number of quantifiers allowed in the invariant')
        s.add_argument('--cvc4-minimize-models',  action=utils.YesNoAction, default=True, help='Minimize models when using CVC4')

    return result
