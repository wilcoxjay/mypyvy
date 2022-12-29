'''Module containing interface to SMT solvers.

Right now it contains the interface to Z3. In the future, it will
contain generic interface, and the Z3 interface will be in
solver_z3.py.

'''
from __future__ import annotations
from collections import OrderedDict, defaultdict
from contextlib import contextmanager
from datetime import datetime
import time
import itertools
import math
import random
import io
import subprocess
import sys
from enum import Enum
from typing import List, Optional, Set, Tuple, Union, Iterable, Dict, Sequence, Iterator
from typing import cast, Callable

import z3

import utils
import typechecker
import syntax
from syntax import Expr, Scope, ConstantDecl, RelationDecl, SortDecl
from syntax import FunctionDecl, DefinitionDecl, Not, New
from semantics import Trace, State, FirstOrderStructure
from translator import Z3Translator, TRANSITION_INDICATOR
from solver_cvc4 import CVC4Model, new_cvc4_process, check_with_cvc4

CheckSatResult = z3.CheckSatResult

sat = z3.sat
unsat = z3.unsat
unknown = z3.unknown


def result_from_z3(res: z3.CheckSatResult) -> CheckSatResult:
    if res == z3.sat:
        return sat
    elif res == z3.unsat:
        return unsat
    elif res == z3.unknown:
        return unknown
    else:
        assert False, res


LatorFactory = Callable[[syntax.Scope, int], Z3Translator]
class Solver:
    def __init__(
            self,
            include_program: bool = True,
            use_cvc4: bool = False,
            translator_factory: Optional[LatorFactory] = None,
            reassert_axioms: bool = False,
            additional_mutable_axioms: List[Expr] = []
    ) -> None:
        self.z3solver = z3.Solver()
        prog = syntax.the_program
        assert prog.scope is not None
        assert len(prog.scope.stack) == 0
        self.scope = cast(Scope[z3.ExprRef], prog.scope)
        self.translator_factory: LatorFactory = translator_factory if translator_factory is not None else Z3Translator
        self.num_states = 0  # number of states for which axioms are assumed so far
        self.nqueries = 0
        self.assumptions_necessary = False
        self.mutable_axioms: List[Expr] = []
        self.stack: List[List[z3.ExprRef]] = [[]]
        self.include_program = include_program
        self.use_cvc4 = use_cvc4
        self.cvc4_proc: Optional[subprocess.Popen] = None
        self.cvc4_last_query: Optional[str] = None
        self.cvc4_last_model_response: Optional[str] = None
        self.cvc4_model: Optional[CVC4Model] = None  # model of the last check(), only used with cvc4 models

        self._init_axioms(prog, include_program, reassert_axioms, additional_mutable_axioms)

    def _init_axioms(self, prog: syntax.Program, include_program: bool,
                     reassert_axioms: bool, additional_mutable_axioms: List[Expr]) -> None:
        axioms = []
        mutable_axioms = []
        if include_program:
            if not reassert_axioms:
                axioms += [a.expr for a in prog.axioms()]
            else:
                mutable_axioms += [a.expr for a in prog.axioms()]

            mutable_axioms += [r.derived_axiom for r in prog.derived_relations()
                               if r.derived_axiom is not None]

        mutable_axioms += additional_mutable_axioms

        t = self.get_translator(0)
        for aexpr in axioms:
            self.add(t.translate_expr(aexpr))

        self.register_mutable_axioms(mutable_axioms)

    def get_cvc4_proc(self) -> subprocess.Popen:
        if self.cvc4_proc is None:
            self.cvc4_proc = new_cvc4_process()
        return self.cvc4_proc

    def debug_recent(self) -> Tuple[str, Optional[str], Optional[str]]:
        return (self.z3solver.to_smt2(), self.cvc4_last_query, self.cvc4_last_model_response)

    def restart(self) -> None:
        print('z3solver restart!')
        self.z3solver = z3.Solver()
        for i, frame in enumerate(self.stack):
            if i > 0:
                self.z3solver.push()
            for e in frame:
                self.z3solver.add(e)

    def register_mutable_axioms(self, axioms: Iterable[Expr]) -> None:
        # ODED: discuss mutable axioms with James
        assert self.include_program
        assert self.num_states == 0, 'mutable axioms must be registered before any states!'
        self.mutable_axioms.extend(axioms)

    def add_states(self, num_states: int) -> None:
        assert self.include_program
        assert self.z3solver.num_scopes() == 0, (
            'the first time get_translator is called with new states, '
            'there must be no scopes pushed on the Z3 stack!'
        )
        t = self.translator_factory(self.scope, num_states)
        for i in range(self.num_states, num_states):
            for a in self.mutable_axioms:
                self.add(t.translate_expr(New(a, i)))
        self.num_states = num_states

    def get_translator(self, num_states: int) -> Z3Translator:
        assert self.include_program
        assert self.z3solver.num_scopes() == 0, (
            'get_translator must be called with no scopes pushed on the Z3 stack!'
        )
        if num_states > self.num_states:
            self.add_states(num_states)
        return self.translator_factory(self.scope, num_states)

    @contextmanager
    def mark_assumptions_necessary(self) -> Iterator[None]:
        old = self.assumptions_necessary
        self.assumptions_necessary = True
        yield None
        self.assumptions_necessary = old

    def push(self) -> None:
        self.stack.append([])
        self.z3solver.push()

    def pop(self) -> None:
        self.stack.pop()
        self.z3solver.pop()

    @contextmanager
    def new_frame(self) -> Iterator[None]:
        self.push()
        yield None
        self.pop()

    def add(self, e: z3.ExprRef) -> None:
        # if logger.isEnabledFor(logging.DEBUG):
        #     logger.debug('adding %s' % e)

        self.stack[-1].append(e)
        self.z3solver.add(e)

    def check(self, assumptions: Optional[Sequence[z3.ExprRef]] = None) -> CheckSatResult:
        # logger.debug('solver.check')
        self.cvc4_model = None
        if assumptions is None:
            assert not self.assumptions_necessary
            assumptions = []
        self.nqueries += 1

        if self.use_cvc4:
            assert assumptions is None or len(assumptions) == 0, 'assumptions not supported in cvc4'
            cvc4_result, model = check_with_cvc4(self.get_cvc4_proc(), self.z3solver.to_smt2())
            self.cvc4_model = model
            return cvc4_result

        def luby() -> Iterable[int]:
            l: List[int] = [1]
            k = 1
            i = 0
            while True:
                while i < len(l):
                    yield l[i]
                    i += 1
                l.extend(l)
                l.append(2 ** k)
                k += 1

        if 'restarts' not in utils.args or not utils.args.restarts:
            res = self.z3solver.check(*assumptions)
            if res == z3.unknown:
                print(f'[{datetime.now()}] Solver.check: encountered unknown, printing debug information')
                print(f'[{datetime.now()}] Solver.check: z3.solver.reason_unknown: {self.z3solver.reason_unknown()}')
                print(f'[{datetime.now()}] Solver.check: self.assertions:')
                for e in self.assertions():
                    print(e)
                print(f'[{datetime.now()}] Solver.check: assumptions:')
                for e in assumptions:
                    print(e)
                print()
                print(f'[{datetime.now()}] Solver.check: self.z3solver stats and smt2:')
                print(self.z3solver.statistics())
                print()
                print(self.z3solver.to_smt2())
                print()

                print(f'[{datetime.now()}] Solver.check: trying fresh solver')
                s2 = z3.Solver()
                for e in self.assertions():
                    s2.add(e)
                res = s2.check(*assumptions)
                print(f'[{datetime.now()}] Solver.check: s2.check(): {res}')
                print(f'[{datetime.now()}] Solver.check: s2 stats and smt2:')
                print(s2.statistics())
                print()
                print(s2.to_smt2())
                print()
                if res == z3.sat:
                    # we can't get model, so we still consider this to be unknown
                    res = z3.unknown

                print(f'[{datetime.now()}] Solver.check: trying fresh context')
                ctx = z3.Context()
                s3 = z3.Solver(ctx=ctx)
                for e in self.assertions():
                    s3.add(e.translate(ctx))
                res = s3.check(*(e.translate(ctx) for e in assumptions))
                print(f'[{datetime.now()}] Solver.check: s3.check(): {res}')
                print(f'[{datetime.now()}] Solver.check: s3 stats and smt2:')
                print(s3.statistics())
                print()
                print(s3.to_smt2())
                print()
                if res == z3.sat:
                    # we can't get model, so we still consider this to be unknown
                    res = z3.unknown

                if assumptions is None or len(assumptions) == 0:
                    print(f'[{datetime.now()}] Solver.check: trying cvc4')
                    cvc4_result, model = check_with_cvc4(self.get_cvc4_proc(), self.z3solver.to_smt2())
                    self.cvc4_model = model
                    print(f'[{datetime.now()}] Solver.check: cvc4 result: {cvc4_result}')
                    res = cvc4_result

            return result_from_z3(res)

        unit = 600000
        num_restarts = 0
        max_restarts = 10000
        for t in luby():
            assert num_restarts <= max_restarts, 'exhausted restart budget. exiting.'
            tmt = t * unit
            self.z3solver.set('timeout', tmt)
            t_start = time.time()
            ans = self.z3solver.check(*assumptions)
            if ans != z3.unknown:
                assert ans in (z3.sat, z3.unsat)
                if num_restarts > 0:
                    print(f'z3solver successful after {1000*(time.time() - t_start):.1f}ms: {ans}')
                return result_from_z3(ans)
            print(f'z3solver returned {ans} after {1000*(time.time() - t_start):.1f}ms '
                  f'(timeout was {tmt}ms), trying again')
            num_restarts += 1
            self.restart()

        assert False

    def model(
            self,
            assumptions: Optional[Sequence[z3.ExprRef]] = None,
            minimize: Optional[bool] = None,
            sorts_to_minimize: Optional[Iterable[z3.SortRef]] = None,
            relations_to_minimize: Optional[Iterable[z3.FuncDeclRef]] = None,
    ) -> z3.ModelRef:
        if self.cvc4_model is not None:
            return cast(z3.ModelRef, self.cvc4_model)
        assert not self.use_cvc4, 'using cvc4 but self.cvc4_model is None!'
        if minimize is None:
            minimize = utils.args.minimize_models
        if minimize:
            if sorts_to_minimize is None:
                sorts_to_minimize = [Z3Translator.sort_to_z3(s) for s in self.scope.sorts.values()
                                     if not syntax.has_annotation(s, 'no_minimize')]
            if relations_to_minimize is None:
                m = self.z3solver.model()
                ds = {str(d) for d in m.decls()}
                rels_to_minimize = []
                for r in self.scope.relations.values():
                    if r.is_derived() or syntax.has_annotation(r, 'no_minimize'):
                        continue
                    if not r.mutable:
                        z3r = Z3Translator.relation_to_z3(r, None)
                        if isinstance(z3r, z3.ExprRef):
                            rels_to_minimize.append(z3r.decl())
                        else:
                            rels_to_minimize.append(z3r)
                    else:
                        # ODED: TODO: think about this, using keys here seems strange
                        for k in Z3Translator._get_keys(self.num_states):
                            z3r = Z3Translator.relation_to_z3(r, k)
                            if isinstance(z3r, z3.ExprRef):
                                z3r = z3r.decl()
                            if str(z3r) in ds:
                                rels_to_minimize.append(z3r)

            return self._minimal_model(assumptions, sorts_to_minimize, rels_to_minimize)
        else:
            return self.z3solver.model()

    def _cardinality_constraint(self, x: Union[z3.SortRef, z3.FuncDeclRef], n: int) -> z3.ExprRef:
        if isinstance(x, z3.SortRef):
            return self._sort_cardinality_constraint(x, n)
        else:
            return self._relational_cardinality_constraint(x, n)

    def _sort_cardinality_constraint(self, s: z3.SortRef, n: int) -> z3.ExprRef:
        x = z3.Const('x$', s)
        disjs = []
        for i in range(n):
            c = z3.Const(f'card$_{s.name()}_{i}', s)
            disjs.append(x == c)

        return z3.ForAll(x, z3.Or(*disjs))

    def _relational_cardinality_constraint(self, relation: z3.FuncDeclRef, n: int) -> z3.ExprRef:
        if relation.arity() == 0:
            return z3.BoolVal(True)

        consts = [[z3.Const(f'card$_{relation}_{i}_{j}', relation.domain(j))
                   for j in range(relation.arity())]
                  for i in range(n)]

        vs = [z3.Const(f'x$_{relation}_{j}', relation.domain(j)) for j in range(relation.arity())]

        result = z3.ForAll(vs, z3.Implies(relation(*vs), z3.Or(*(
            z3.And(*(
                c == v for c, v in zip(cs, vs)
            ))
            for cs in consts
        ))))
        return result

    def _minimal_model(
            self,
            assumptions: Optional[Sequence[z3.ExprRef]],
            sorts_to_minimize: Iterable[z3.SortRef],
            relations_to_minimize: Iterable[z3.FuncDeclRef],
    ) -> z3.ModelRef:
        assert not self.use_cvc4, 'minimizing models is only for z3'
        with self.new_frame():
            for x in itertools.chain(
                    cast(Iterable[Union[z3.SortRef, z3.FuncDeclRef]], sorts_to_minimize),
                    relations_to_minimize):
                for n in itertools.count(1):
                    with self.new_frame():
                        self.add(self._cardinality_constraint(x, n))
                        res = self.check(assumptions)
                        assert res in (sat, unsat), res
                        if res == z3.sat:
                            break
                self.add(self._cardinality_constraint(x, n))

            assert self.check(assumptions) == z3.sat
            return self.z3solver.model()

    def assertions(self) -> Sequence[z3.ExprRef]:
        asserts = self.z3solver.assertions()
        return sorted(asserts, key=lambda x: str(x))

    def unsat_core(self) -> Sequence[z3.ExprRef]:
        return self.z3solver.unsat_core()

    def reason_unknown(self) -> str:
        return self.z3solver.reason_unknown()
