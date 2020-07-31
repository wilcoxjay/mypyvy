'''
Experiments in separation using "QBF" solvers
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
from contextlib import contextmanager

from syntax import *
from logic import *

from typing import TypeVar, Iterable, FrozenSet, Union, Callable, Generator, Set, Optional, cast, Type, Collection, TYPE_CHECKING, AbstractSet, Iterator

from pd import cheap_check_implication
import z3

@contextmanager
def z3_full_print(max_width: int = 200) -> Iterator[None]:
    old_values: Dict[Tuple[str, str], int] = {}
    inf = float('inf')
    to_change = {
        ('_Formatter', 'max_args'): inf,
        ('_Formatter', 'max_depth'): inf,
        ('_Formatter', 'max_visited'): inf,
        ('_PP', 'max_indent'): inf,
        ('_PP', 'max_lines'): inf,
        ('_PP', 'max_width'): max_width,
    }
    for x, y in to_change:
        obj = getattr(z3.z3printer, x)
        v = getattr(obj, y)
        assert isinstance(v, int)
        old_values[x, y] = v
        setattr(obj, y, to_change[x, y])
    try:
        yield
    finally:
        for x, y in to_change:
            setattr(getattr(z3.z3printer, x), y, old_values[x, y])


def sep_main(solver: Solver) -> str:
    prog = syntax.the_program
    print(f'\n[{datetime.now()}] [PID={os.getpid()}] Starting sep\n')

    safety = tuple(chain(*(as_clauses(inv.expr) for inv in prog.invs() if inv.is_safety))) # convert to CNF
    invs = tuple(chain(*(as_clauses(inv.expr) for inv in prog.invs() if not inv.is_safety))) # convert to CNF
    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # convert to CNF
    assert cheap_check_implication(inits, safety), 'Initial states not safe'
    assert not cheap_check_implication(chain(invs, safety), inits), 'Some initial condition is actually invariant'

    for i, p in enumerate(safety):
        print(f'Safety {i}: {p}')
    print()
    for i, p in enumerate(invs):
        print(f'Invariant {i}: {p}')
    print()

    # just for testing, get a model of invs that violates every init predicate
    t = solver.get_translator(1)
    with solver.new_frame():
        solver.add(t.translate_expr(Not(And(*inits))))
        for e in chain(safety, invs):
            solver.add(t.translate_expr(e))
        res = solver.check()
        assert res == z3.sat, f'{res}\n{solver.z3solver}'
        m0 = Z3Translator.model_to_trace(solver.model(minimize=True), 1).as_state(0)
        print(f'Using the following model:\n\n{m0}\n')

    print(f'[{datetime.now()}] Learning {len(invs)} invariants one by one')
    seen: Set[str] = set() # used to ensure we don't declare conflicting z3 symbols
    n_total_cex = 1
    n_learned = 0
    for i, p in reversed(list(enumerate(invs))):
        print(f'\n\n\n[{datetime.now()}] Learning invariant {i}: {p}\n')
        solver = Solver(use_cvc4=utils.args.cvc4) # reusing the same solver too much results in unknowns
        prefix: List[str] = []
        prefix_sorts: List[UninterpretedSort] = []
        vs: List[SortedVar] = []

        if isinstance(p, QuantifierExpr):
            assert p.quant == 'FORALL'
            prefix = []
            for v in p.vs():
                assert isinstance(v.sort, UninterpretedSort)
                prefix.append(v.sort.name)
                prefix_sorts.append(v.sort)
            vs = [SortedVar(f'V{i}', s) for i, s in enumerate(prefix_sorts)]

        var_names = [v.name for v in vs]

        terms: Dict[str, List[Expr]] = defaultdict(list)
        def print_terms(msg: str = 'terms') -> None:
            print(f'[{datetime.now()}] {msg} ({sum(len(ts) for ts in terms.values())}):')
            for k in sorted(terms.keys()):
                print(f'{k:10} ({len(terms[k]):4}): ' + ' '.join(sorted(str(t) for t in terms[k])))
            print()
        atomic_terms: List[Union[SortedVar, ConstantDecl]] = list(chain(vs, prog.constants()))
        for x in atomic_terms:
            assert isinstance(x.sort, UninterpretedSort)
            terms[x.sort.name].append(Id(x.name))
        print_terms('atomic terms')

        # add function applications, only to depth 1 (can iterate to get deeper terms)
        terms0 = defaultdict(list, {k: list(v) for k, v in terms.items()})
        for f in prog.functions():
            assert len(f.arity) > 0
            assert isinstance(f.sort, UninterpretedSort)
            arg_sorts: List[str] = []
            for s in f.arity:
                assert isinstance(s, UninterpretedSort)
                arg_sorts.append(s.name)
            for ts in product(*(terms0[name] for name in arg_sorts)):
                terms[f.sort.name].append(Apply(f.name, list(ts)))
        print_terms('terms with functions')

        atoms: List[Expr] = []
        for r in prog.relations():
            if len(r.arity) == 0:
                atoms.append(Id(r.name))
                continue
            arg_sorts = []
            for s in r.arity:
                assert isinstance(s, UninterpretedSort)
                arg_sorts.append(s.name)
            for ts in product(*(terms[name] for name in arg_sorts)):
                atoms.append(Apply(r.name, list(ts)))
        atoms.extend(Eq(x, y) for ts in terms.values() for x, y in combinations(ts, 2))
        atoms = sorted(atoms)
        print(f'[{datetime.now()}] atoms ({len(atoms)}):\n' + ''.join(f'    {a}\n' for a in atoms))
        literals = [lit for a in atoms for lit in [a, Not(a)]]
        print(f'[{datetime.now()}] literals ({len(literals)}):\n' + ''.join(f'{i:8}: {lit}\n' for i, lit in enumerate(literals)))

        n_clauses = 1
        xs: Dict[Tuple[int, Expr], z3.ExprRef] = {
            (i, lit): z3.Bool(f'x_{i}_{j}')
            for i in range(n_clauses)
            for j, lit in enumerate(literals)
        }

        def eval_sep(
                state: State,
                st_prefix: Optional[str] = None
        ) -> Tuple[List[z3.ExprRef], z3.ExprRef]:
            '''
            returns (assertions, v), where assertions need to be asserted in the solver, and then v encodes whether state satisfies the separator or not.
            '''
            st_prefix_ = st_prefix if st_prefix is not None else f'state_{id(state)}_{len(seen)}'
            def p(st: str, must_be_new: bool = True) -> str:
                st = st_prefix_ + '_' + st
                assert (not must_be_new) or st not in seen, (st, seen)
                seen.add(st)
                return st
            assertions: List[z3.ExprRef] = []
            state_models_sep = z3.Bool(p('models_sep'))
            # create z3 symbols for all relations, functions, and constants, and assert their meaning

            # create universe unary relations
            scope = max(len(elems) for elems in state.univs().values())
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
            universes = {s.name: z3.Function(p(s.name), V, z3.BoolSort()) for s in state.univs()}
            elem_to_z3: Dict[str, z3.ExprRef] = {}
            for s, elems in state.univs().items():
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
                for r in state.rel_interp()
            }
            for r, ri in state.rel_interp().items():
                if len(r.arity) == 0:
                    assert len(ri) == 1 and len(ri[0][0]) == 0, (r, ri)
                    a = relations[r.name]
                    assert isinstance(a, z3.ExprRef)
                    assertions.append(lit(a, ri[0][1]))
                else:
                    for tup, polarity in ri:
                        a = relations[r.name]
                        assert isinstance(a, z3.FuncDeclRef)
                        args = [elem_to_z3[x] for x in tup]
                        assertions.append(lit(a(*args), polarity))

            # create functions
            assert all(len(f.arity) > 0 for f in state.func_interp())
            functions: Dict[str, z3.FuncDeclRef] = {
                f.name:
                z3.Function(p(f.name), *repeat(V, len(f.arity)), V)
                for f in state.func_interp()
            }
            for f, fi in state.func_interp().items():
                for tup, img in fi:
                    args = [elem_to_z3[x] for x in tup]
                    assertions.append(functions[f.name](*args) == elem_to_z3[img])

            # create constants
            constants: Dict[str, z3.ExprRef] = {
                c.name: z3.Const(p(c.name), V)
                for c in state.const_interp()
            }
            for c, ci in state.const_interp().items():
                assertions.append(constants[c.name] == elem_to_z3[ci])

            # now force state_models_sep
            z3_vs = [z3.Const(p(f'V{i}'), V) for i, s in enumerate(prefix)]
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
                else:
                    assert False, e
            value = z3.Implies(
                z3.And(*(
                    universes[s](v)
                    for v, s in zip(z3_vs, prefix)
                )),
                z3.And(*(
                    z3.Or(*(
                        z3.And(xs[i, lit], to_z3(lit))
                        for lit in literals
                    ))
                    for i in range(n_clauses)
                ))
            )
            if len(z3_vs) > 0:
                value = z3.ForAll(z3_vs, value)
            assertions.append(state_models_sep == value)

            return assertions, state_models_sep

        assertions, m0_models_sep = eval_sep(
            m0,
            f'm0_{i}',
        )
        print(f'[{datetime.now()}] Assertions for m0 are:')
        with z3_full_print():
            for a in assertions:
                print(a)
        print('\n\n')

        z3sep = z3.Solver()
        for a in assertions:
            z3sep.add(a)
        z3sep.add(m0_models_sep)
        n_cex = 0
        while True:
            res = z3sep.check()
            assert res in (z3.sat, z3.unsat), f'{res}\n\n{z3sep}'
            if res == z3.unsat:
                n_total_cex += n_cex
                print(f'[{datetime.now()}] Failure! Cannot learn invariant {i} after {n_cex} counterexamples. Maybe it has function depth more than 1?\n    {p}\n\n')
                break
            model = z3sep.model()
            # bias toward strongest separator, but no minimization for now
            assignment: Dict[Tuple[int, Expr], bool] = {
                k: z3.is_true(model[x])
                for k, x in xs.items()
            }
            sep = Forall(vs, And(*(
                Or(*(lit for lit in literals if assignment[i, lit]))
                for i in range(n_clauses)
            )))
            print(f'[{datetime.now()}] Candidate separator is: {sep}\n')
            z3cex = check_implication(solver, [p], [sep], minimize=True)
            if z3cex is not None:
                cex = Z3Translator.model_to_trace(z3cex, 1).as_state(0)
                print(f'[{datetime.now()}] Got positive counterexample:\n\n{cex}\n')
                assertions, cex_models_sep = eval_sep(cex)
                for a in assertions:
                    z3sep.add(a)
                z3sep.add(cex_models_sep)
                n_cex += 1
                continue
            z3cex = check_implication(solver, [sep], [p], minimize=True)
            if z3cex is not None:
                cex = Z3Translator.model_to_trace(z3cex, 1).as_state(0)
                print(f'[{datetime.now()}] Got negative counterexample:\n\n{cex}\n')
                assertions, cex_models_sep = eval_sep(cex)
                for a in assertions:
                    z3sep.add(a)
                z3sep.add(z3.Not(cex_models_sep))
                n_cex += 1
                continue
            n_total_cex += n_cex
            n_learned += 1
            print(f'[{datetime.now()}] Success! Learned invariant {i} after {n_cex} counterexamples:\n    {sep}\n    <=>\n    {p}\n\n')
            break

        # # This is a version that scales very poorly, and does not use
        # # any additional solver symbols. After very preliminary
        # # experiments, I decided to use solver symbols that encode
        # # relations, functions, and constants of the model.
        #
        # V = z3.Datatype('V')
        # for i in range(10):
        #     V.declare(f'e{i}')
        # V = V.create()
        #
        # def eval_sep(universe: Dict[str, int], # for each sort, how many elements n - elements are 0,...,n-1
        #              relations: Dict[str, Dict[Tuple[int, ...], bool]], # for each relation, mapping to bool
        #              functions: Dict[str, Dict[Tuple[int, ...], int]], # for each function, mapping
        #              constants: Dict[str, int], # value of each constant
        # ) -> z3.ExprRef:
        #     z3_vs = [z3.Const(f'V{i}', V) for i, s in enumerate(prefix)]
        #     def eval_lit(lit: Expr) -> z3.ExprRef:
        #         free_vars = sorted(int(n[1:]) for n in lit.free_ids() if n in var_names)
        #         def lit_true(vals: Tuple[int, ...]) -> bool:
        #             def tt(t: Expr) -> int:
        #                 'evaluate term under current assignment'
        #                 if isinstance(t, Id):
        #                     if t.name in var_names and int(t.name[1:]) in free_vars:
        #                         return vals[free_vars.index(int(t.name[1:]))]
        #                     else:
        #                         return constants[t.name]
        #                 elif isinstance(t, AppExpr):
        #                     return functions[t.callee][tuple(map(tt, t.args))]
        #                 else:
        #                     assert False
        #             if isinstance(lit, UnaryExpr) and lit.op == 'NOT':
        #                 a = lit.arg
        #             else:
        #                 a = lit
        #             if isinstance(a, Id):
        #                 res = relations[a.name][()]
        #             elif isinstance(a, AppExpr):
        #                 res = relations[a.callee][tuple(map(tt, a.args))]
        #             elif isinstance(a, BinaryExpr) and a.op == 'EQUAL':
        #                 res = tt(a.arg1) == tt(a.arg2)
        #             else:
        #                 assert False, a
        #             if isinstance(lit, UnaryExpr) and lit.op == 'NOT':
        #                 return not res
        #             else:
        #                 return res
        #         true_vals = [
        #             vals
        #             for vals in product(*(
        #                     range(universe[prefix[i]])
        #                     for i in free_vars
        #             ))
        #             if lit_true(vals)
        #         ]
        #         return z3.Or(*(
        #             z3.And(*(
        #                 getattr(V, f'is_e{v}')(z3_vs[i])
        #                 for i, v in zip(free_vars, vals)
        #             ))
        #             for vals in true_vals
        #         ))
        #     body = z3.Implies(
        #         z3.And(*(
        #             z3.Or(*(
        #                 getattr(V, f'is_e{i}')(v)
        #                 for i in range(universe[s])
        #             ))
        #             for v, s in zip(z3_vs, prefix)
        #         )),
        #         z3.And(*(
        #             z3.Or(*(
        #                 z3.And(xs[i, lit], eval_lit(lit))
        #                 for lit in literals
        #             ))
        #             for i in range(n_clauses)
        #         ))
        #     )
        #     if len(z3_vs) == 0:
        #         return body
        #     else:
        #         return z3.ForAll(z3_vs, body)
        # print(eval_sep(
        #     defaultdict(lambda: 2),
        #     defaultdict(lambda: defaultdict(lambda: True)),
        #     defaultdict(lambda: defaultdict(int)),
        #     defaultdict(int),
        # ))
        #
        # assert False

    print(f'[{datetime.now()}] Successfully learned a total of {n_learned} out of {len(invs)} invariants one by one using a total of {n_total_cex} examples.')

    return 'yo'


def add_argparsers(subparsers: argparse._SubParsersAction) -> Iterable[argparse.ArgumentParser]:
    result : List[argparse.ArgumentParser] = []

    # sep
    s = subparsers.add_parser('sep', help='Run the experimental separation code')
    s.set_defaults(main=sep_main)
    result.append(s)

    return result
