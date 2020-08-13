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


class UniversalFixedPrefixSep:
    def __init__(self,
                 prefix_sorts: Tuple[UninterpretedSort, ...],
                 states: List[State],  # assumed to only grow, indices are used as "state keys"
    ):
        self.prog = syntax.the_program
        self.states = states
        self.prefix_sorts = prefix_sorts
        self.prefix_names = tuple(s.name for s in prefix_sorts)
        self.vs = tuple(SortedVar(f'V{i}', s) for i, s in enumerate(prefix_sorts))
        self.var_names = tuple(v.name for v in self.vs)

        # generate terms, atoms, and literals
        terms: Dict[str, List[Expr]] = defaultdict(list)
        def print_terms(msg: str = 'terms') -> None:
            print(f'[{datetime.now()}] {msg} ({sum(len(ts) for ts in terms.values())}):')
            for k in sorted(terms.keys()):
                print(f'{k:10} ({len(terms[k]):4}): ' + ' '.join(sorted(str(t) for t in terms[k])))
            print()
        atomic_terms: List[Union[SortedVar, ConstantDecl]] = list(chain(self.vs, self.prog.constants()))
        for x in atomic_terms:
            assert isinstance(x.sort, UninterpretedSort)
            terms[x.sort.name].append(Id(x.name))
        print_terms('atomic terms')
        # add function applications, only to depth 1 (can iterate to get deeper terms)
        terms0 = defaultdict(list, {k: list(v) for k, v in terms.items()})
        for f in self.prog.functions():
            assert len(f.arity) > 0
            assert isinstance(f.sort, UninterpretedSort)
            arg_sorts: List[str] = []
            for s in f.arity:
                assert isinstance(s, UninterpretedSort)
                arg_sorts.append(s.name)
            for ts in product(*(terms0[name] for name in arg_sorts)):
                terms[f.sort.name].append(Apply(f.name, ts))
        print_terms('terms with functions')
        # atoms
        atoms: List[Expr] = []
        for r in self.prog.relations():
            if len(r.arity) == 0:
                atoms.append(Id(r.name))
                continue
            arg_sorts = []
            for s in r.arity:
                assert isinstance(s, UninterpretedSort)
                arg_sorts.append(s.name)
            for ts in product(*(terms[name] for name in arg_sorts)):
                atoms.append(Apply(r.name, ts))
        atoms.extend(Eq(x, y) for ts in terms.values() for x, y in combinations(ts, 2))
        atoms = sorted(atoms)
        print(f'[{datetime.now()}] atoms ({len(atoms)}):\n' + ''.join(f'    {a}\n' for a in atoms))
        # literals
        literals = tuple(lit for a in atoms for lit in (a, Not(a)))
        print(f'[{datetime.now()}] literals ({len(literals)}):\n' + ''.join(f'{i:8}: {lit}\n' for i, lit in enumerate(literals)))
        self.literals = literals

        self.n_clauses = 1
        self.lit_vs: Dict[Tuple[int, Expr], z3.ExprRef] = {
            (i, lit): z3.Bool(f'lit_{i}_{j}')
            for i in range(self.n_clauses)
            for j, lit in enumerate(self.literals)
        }

        self.state_vs: Dict[int, z3.ExprRef] = {}  # state_vs[i] represents the value of the separator in self.states[i]

        self.solver = z3.Solver()
        self.seen: Set[str] = set()  # used to assert we don't have name collisions

    def separate(self,
                 pos: Collection[int] = (),
                 neg: Collection[int] = (),
    ) -> Optional[Expr]:
        assert all(0 <= i < len(self.states) for i in chain(pos, neg))
        assumptions = tuple(chain(
            (self.state_v(i) for i in sorted(pos)),
            (z3.Not(self.state_v(i)) for i in sorted(neg)),
        ))
        res = self.solver.check(*assumptions)
        assert res in (z3.sat, z3.unsat), f'{res}\n\n{self.solver}'
        if res == z3.unsat:
            return None
        else:
            m = self.solver.model()
            # bias toward strongest separator, but no minimization for now
            assignment: Dict[Tuple[int, Expr], bool] = {
                k: z3.is_true(m[x])
                for k, x in self.lit_vs.items()
            }
            return Forall(self.vs, And(*(
                Or(*(lit for lit in self.literals if assignment[i, lit]))
                for i in range(self.n_clauses)
            )))

    def state_v(self, i: int) -> z3.ExprRef:
        assert 0 <= i < len(self.states)
        if i not in self.state_vs:
            assertions, self.state_vs[i] = self._eval_sep(self.states[i], f'state_{i}')
            for a in assertions:
                self.solver.add(a)
        return self.state_vs[i]

    def _eval_sep(self, state: State, st_prefix: str) -> Tuple[List[z3.ExprRef], z3.ExprRef]:
        '''
        create new state variable add assertions enforcing its value
        '''
        def p(st: str, must_be_new: bool = True) -> str:
            st = st_prefix + '_' + st
            assert (not must_be_new) or st not in self.seen, (st, self.seen)
            self.seen.add(st)
            return st

        assertions: List[z3.ExprRef] = []  # will be added to the solver
        state_models_sep = z3.Bool(p('models_sep'))  # will become self.state_vs[i]

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

        # now force state_models_sep
        z3_vs = [z3.Const(p(f'V{i}'), V) for i in range(len(self.vs))]
        def to_z3(e: Expr) -> z3.ExprRef:
            if isinstance(e, Id):
                if e.name in self.var_names:
                    return z3_vs[self.var_names.index(e.name)]
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
                for v, s in zip(z3_vs, self.prefix_names)
            )),
            z3.And(*(
                z3.Or(*(
                    z3.And(self.lit_vs[i, lit], to_z3(lit))
                    for lit in self.literals
                ))
                for i in range(self.n_clauses)
            ))
        )
        if len(z3_vs) > 0:
            value = z3.ForAll(z3_vs, value)
        assertions.append(state_models_sep == value)

        return assertions, state_models_sep



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

    # just for testing, get a model of invs that violates some init predicate
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
    states: List[State] = [m0]
    n_total_cex = 1
    n_learned = 0
    for i, p in reversed(list(enumerate(invs))):
        print(f'\n\n\n[{datetime.now()}] Learning invariant {i}: {p}\n')
        solver = Solver(use_cvc4=utils.args.cvc4) # reusing the same solver too much results in unknowns

        prefix_sorts: List[UninterpretedSort] = []
        if isinstance(p, QuantifierExpr):
            assert p.quant == 'FORALL'
            for v in p.get_vs():
                assert isinstance(v.sort, UninterpretedSort)
                prefix_sorts.append(v.sort)
        separator = UniversalFixedPrefixSep(tuple(prefix_sorts), states)

        pos: List[int] = [0]
        neg: List[int] = []
        n_cex = 0
        while True:
            sep = separator.separate(pos, neg)
            if sep is None:
                n_total_cex += n_cex
                print(f'[{datetime.now()}] Failure! Cannot learn invariant {i} after {n_cex} counterexamples. Maybe it has function depth more than 1?\n    {p}\n\n')
                break
            print(f'[{datetime.now()}] Candidate separator is: {sep}\n')
            z3cex = check_implication(solver, [p], [sep], minimize=True)
            if z3cex is not None:
                cex = Z3Translator.model_to_trace(z3cex, 1).as_state(0)
                print(f'[{datetime.now()}] Got positive counterexample:\n\n{cex}\n')
                pos.append(len(states))
                states.append(cex)
                n_cex += 1
                continue
            z3cex = check_implication(solver, [sep], [p], minimize=True)
            if z3cex is not None:
                cex = Z3Translator.model_to_trace(z3cex, 1).as_state(0)
                print(f'[{datetime.now()}] Got negative counterexample:\n\n{cex}\n')
                neg.append(len(states))
                states.append(cex)
                n_cex += 1
                continue
            # no cex, i.e., sep <=> p
            n_total_cex += n_cex
            n_learned += 1
            print(f'[{datetime.now()}] Success! Learned invariant {i} after {n_cex} counterexamples:\n    {sep}\n    <=>\n    {p}\n\n')
            break

    print(f'[{datetime.now()}] Successfully learned a total of {n_learned} out of {len(invs)} invariants one by one using a total of {n_total_cex} examples.')

    return 'yo'


def add_argparsers(subparsers: argparse._SubParsersAction) -> Iterable[argparse.ArgumentParser]:
    result : List[argparse.ArgumentParser] = []

    # sep
    s = subparsers.add_parser('sep', help='Run the experimental separation code')
    s.set_defaults(main=sep_main)
    result.append(s)

    return result
