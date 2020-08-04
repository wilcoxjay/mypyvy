from __future__ import annotations
from collections import OrderedDict, defaultdict
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime
import dataclasses
import time
import itertools
import math
import random
import io
import re
import sexp
import subprocess
import sys
from typing import List, Optional, Set, Tuple, Union, Iterable, Dict, Sequence, Iterator
from typing import cast, TypeVar, Callable

import z3

import utils
import typechecker
import syntax
from syntax import Expr, Scope, ConstantDecl, RelationDecl, SortDecl
from syntax import FunctionDecl, DefinitionDecl, Not, New
from semantics import Trace, State, FirstOrderStructure
from translator import Z3Translator, TRANSITION_INDICATOR
from solver_cvc4 import CVC4Model, new_cvc4_process, check_with_cvc4


# useful for debugging
def verbose_print_z3_model(m: z3.ModelRef) -> None:
    utils.logger.always_print('')
    out = io.StringIO()
    fmt = z3.Formatter()  # type: ignore
    fmt.max_args = 10000
    utils.logger.always_print(str(fmt.max_args))
    pp = z3.PP()  # type: ignore
    pp.max_lines = 10000
    pp(out, fmt(m))
    utils.logger.always_print(out.getvalue())
    assert False

def check_solver(s: Solver, num_states: int, minimize: Optional[bool] = None) -> Optional[Trace]:
    res = s.check()
    m = None

    if res != z3.unsat:
        if res != z3.sat:
            assert res == z3.unknown
            utils.logger.always_print('unknown!')
            utils.logger.always_print('reason unknown: ' + s.reason_unknown())
            assert False, 'unexpected unknown from z3!'

        assert res == z3.sat
        m = Z3Translator.model_to_trace(s.model(minimize=minimize), num_states)

    return m

def check_unsat(
        errmsgs: List[Tuple[Optional[syntax.Span], str]],
        s: Solver,
        num_states: int,
        minimize: Optional[bool] = None,
        verbose: bool = True
) -> Optional[Trace]:
    start = datetime.now()
    # if logger.isEnabledFor(logging.DEBUG):
    #     logger.debug('assertions')
    #     logger.debug(str(s.assertions()))

    if (m := check_solver(s, num_states, minimize=minimize)) is not None:
        if verbose:
            utils.logger.always_print('')
            if utils.args.print_counterexample:
                utils.logger.always_print(str(m))

            for span, msg in errmsgs:
                utils.print_error(span, msg)

        return m
    else:
        if verbose:
            if not utils.args.query_time:
                time_msg = ''
            else:
                time_msg = ' (%s)' % (datetime.now() - start, )
            utils.logger.always_print('ok.%s' % (time_msg,))

            sys.stdout.flush()
        return None


def check_init(
        s: Solver,
        safety_only: bool = False,
        minimize: Optional[bool] = None,
        verbose: bool = True
) -> Optional[Tuple[syntax.InvariantDecl, Trace]]:
    if verbose:
        utils.logger.always_print('checking init:')

    prog = syntax.the_program
    t = s.get_translator(1)

    with s.new_frame():
        for init in prog.inits():
            s.add(t.translate_expr(init.expr))

        for inv in (prog.invs() if not safety_only else prog.safeties()):
            with s.new_frame():
                s.add(t.translate_expr(Not(inv.expr)))

                if inv.name is not None:
                    msg = ' ' + inv.name
                elif inv.span is not None:
                    msg = ' on line %d' % inv.span[0].lineno
                else:
                    msg = ''
                if verbose:
                    utils.logger.always_print('  implies invariant%s... ' % msg, end='')
                    sys.stdout.flush()

                res = check_unsat([(inv.span, 'invariant%s does not hold in initial state' % msg)],
                                  s, 1, minimize=minimize, verbose=verbose)
                if res is not None:
                    if utils.args.smoke_test_solver:
                        state = State(res, 0)
                        for ax in prog.axioms():
                            if state.eval(ax.expr) is not True:
                                print('\n\n'.join(str(x) for x in s.debug_recent()))
                                print(res)
                                assert False, f'bad initial counterexample for axiom {ax.expr}'
                        for init in prog.inits():
                            if state.eval(init.expr) is not True:
                                print('\n\n'.join(str(x) for x in s.debug_recent()))
                                print(res)
                                assert False, f'bad initial counterexample for initial condition {init.expr}'
                        if state.eval(inv.expr) is not False:
                            print('\n\n'.join(str(x) for x in s.debug_recent()))
                            print(res)
                            assert False, f'bad initial counterexample for invariant {inv.expr}'

                    return inv, res
    return None

def check_transitions(
        s: Solver,
        minimize: Optional[bool] = None,
        verbose: bool = True
) -> Optional[Tuple[syntax.InvariantDecl, Trace, DefinitionDecl]]:
    lator = s.get_translator(2)
    prog = syntax.the_program

    with s.new_frame():
        for inv in prog.invs():
            s.add(lator.translate_expr(inv.expr))

        for ition in prog.transitions():
            if 'check_transition' in utils.args and \
               utils.args.check_transition is not None and \
               ition.name not in utils.args.check_transition:
                continue

            if verbose:
                utils.logger.always_print('checking transition %s:' % (ition.name,))

            with s.new_frame():
                s.add(lator.translate_expr(ition.as_twostate_formula(prog.scope)))
                for inv in prog.invs():
                    if 'check_invariant' in utils.args and \
                       utils.args.check_invariant is not None and \
                       inv.name not in utils.args.check_invariant:
                        continue

                    with s.new_frame():
                        s.add(lator.translate_expr(New(Not(inv.expr))))

                        if inv.name is not None:
                            msg = ' ' + inv.name
                        elif inv.span is not None:
                            msg = ' on line %d' % inv.span[0].lineno
                        else:
                            msg = ''
                        if verbose:
                            utils.logger.always_print('  preserves invariant%s... ' % msg, end='')
                            sys.stdout.flush()

                        res = check_unsat([(inv.span, 'invariant%s is not preserved by transition %s'
                                            % (msg, ition.name)),
                                           (ition.span, 'this transition does not preserve invariant%s'
                                            % (msg,))],
                                          s, 2, minimize=minimize, verbose=verbose)
                        if res is not None:
                            if utils.args.smoke_test_solver:
                                pre_state = res.as_state(i=0)
                                for ax in prog.axioms():
                                    if pre_state.eval(ax.expr) is not True:
                                        print('\n\n'.join(str(x) for x in s.debug_recent()))
                                        print(res)
                                        assert False, f'bad transition counterexample for axiom {ax.expr} in pre state'
                                for pre_inv in prog.invs():
                                    if pre_state.eval(pre_inv.expr) is not True:
                                        print('\n\n'.join(str(x) for x in s.debug_recent()))
                                        print(res)
                                        msg = f'bad transition counterexample for invariant {pre_inv.expr} in pre state'
                                        assert False, msg
                                # need to implement mypyvy-level transition->expression translation
                                # res.eval_double_vocabulary(transition, start_location=0)
                                post_state = res.as_state(i=1)
                                if post_state.eval(inv.expr) is not False:
                                    print('\n\n'.join(str(x) for x in s.debug_recent()))
                                    print(res)
                                    msg = f'bad transition counterexample for invariant {inv.expr} in post state'
                                    assert False, msg

                            return inv, res, ition
    return None

def check_implication(
        s: Solver,
        hyps: Iterable[Expr],
        concs: Iterable[Expr],
        minimize: Optional[bool] = None
) -> Optional[z3.ModelRef]:
    t = s.get_translator(1)
    with s.new_frame():
        for e in hyps:
            s.add(t.translate_expr(e))
        for e in concs:
            with s.new_frame():
                s.add(t.translate_expr(Not(e)))
                if s.check() != z3.unsat:
                    return s.model(minimize=minimize)

    return None

def check_two_state_implication_all_transitions(
        s: Solver,
        old_hyps: Iterable[Expr],
        new_conc: Expr,
        minimize: Optional[bool] = None,
) -> Optional[Tuple[z3.ModelRef, DefinitionDecl]]:
    t = s.get_translator(2)
    prog = syntax.the_program
    with s.new_frame():
        for h in old_hyps:
            s.add(t.translate_expr(h))
        s.add(t.translate_expr(New(Not(new_conc))))
        for trans in prog.transitions():
            with s.new_frame():
                s.add(t.translate_expr(trans.as_twostate_formula(prog.scope)))
                res = s.check()
                assert res in (z3.sat, z3.unsat), res
                if res != z3.unsat:
                    return s.model(minimize=minimize), trans
        return None

def get_transition_indicator(uid: str, name: str) -> str:
    return '%s_%s_%s' % (TRANSITION_INDICATOR, uid, name)

def assert_any_transition(s: Solver, t: Z3Translator,
                          state_index: int, allow_stutter: bool = False) -> None:
    prog = syntax.the_program
    uid = str(state_index)

    tids = []
    for transition in prog.transitions():
        tid = z3.Bool(get_transition_indicator(uid, transition.name))
        tids.append(tid)
        s.add(z3.Implies(tid, t.translate_expr(New(transition.as_twostate_formula(prog.scope), state_index))))

    if allow_stutter:
        tid = z3.Bool(get_transition_indicator(uid, '$stutter'))
        tids.append(tid)
        frame = syntax.And(*DefinitionDecl._frame(prog.scope, mods=()))
        s.add(z3.Implies(tid, t.translate_expr(New(frame, state_index))))

    s.add(z3.Or(*tids))


def check_bmc(s: Solver, safety: Expr, depth: int, preconds: Optional[Iterable[Expr]] = None,
              minimize: Optional[bool] = None) -> Optional[Trace]:
    prog = syntax.the_program

    if preconds is None:
        preconds = (init.expr for init in prog.inits())

    t = s.get_translator(depth + 1)

    with s.new_frame():
        for precond in preconds:
            s.add(t.translate_expr(precond))

        s.add(t.translate_expr(syntax.New(syntax.Not(safety), depth)))

        for i in range(depth):
            s.add(t.translate_expr(New(safety, i)))
            assert_any_transition(s, t, i, allow_stutter=False)

        res = s.check()
        if res == z3.sat:
            z3m = s.model(minimize=minimize)
            m = Z3Translator.model_to_trace(z3m, depth + 1)
            return m
        elif res == z3.unknown:
            print('unknown!')
        return None


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

    def check(self, assumptions: Optional[Sequence[z3.ExprRef]] = None) -> z3.CheckSatResult:
        # logger.debug('solver.check')
        self.cvc4_model = None
        if assumptions is None:
            assert not self.assumptions_necessary
            assumptions = []
        self.nqueries += 1

        if self.use_cvc4:
            assert assumptions is None or len(assumptions) == 0, 'assumptions not supported in cvc4'
            self.cvc4_model = check_with_cvc4(self.get_cvc4_proc(), self.z3solver.to_smt2())
            return z3.unsat if self.cvc4_model is None else z3.sat

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
                # ODED: I comment this out, since the axioms are
                # already supposed to be part of self.assetions():
                # lator = self.translator_factory(self.scope, 0)
                # for a in syntax.the_program.axioms():
                #     s2.add(lator.translate_expr(a.expr))
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
                # ODED: see comment above, axioms should already be in self.assertions()
                # for a in syntax.the_program.axioms():
                #     s3.add(lator.translate_expr(a.expr).translate(ctx))
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
                    self.cvc4_model = check_with_cvc4(self.get_cvc4_proc(), self.z3solver.to_smt2())
                    res = z3.unsat if self.cvc4_model is None else z3.sat
                    print(f'[{datetime.now()}] Solver.check: cvc4 result: {res}')

            assert res in (z3.sat, z3.unsat), (res, self.z3solver.reason_unknown()
                                               if res == z3.unknown else None)
            return res

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
                return ans
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

_RelevantDecl = Union[SortDecl, RelationDecl, ConstantDecl, FunctionDecl]

class Diagram:
    # This class represents a formula of the form
    #
    #     exists X1, ..., X_k.
    #         C1 & C2 & ... & C_n
    #
    # in a way that is slightly more convenient than a usual ast for computing an
    # unsat core of the C_i.  Instead of just an ast, this class stores a list of
    # vars and a list of conjuncts.  In order to make resolution work seamlessly,
    # it also constructs an internal ast of the formula, which structurally shares
    # all the conjuncts from the list.  This ast is ignored except for purposes
    # of resolving all the C_i.

    def __init__(
            self,
            struct: FirstOrderStructure,
    ) -> None:
        vs, ineqs, rels, consts, funcs = Diagram._read_first_order_structure(struct)
        self.binder = syntax.Binder(tuple(vs))
        self.ineqs = ineqs
        self.rels = rels
        self.consts = consts
        self.funcs = funcs
        self.trackers: List[z3.ExprRef] = []
        self.tombstones: Dict[_RelevantDecl, Optional[Set[int]]] = defaultdict(set)
        if utils.args.simplify_diagram:
            self.simplify_consts()
        prog = syntax.the_program
        assert prog.scope is not None
        self._typecheck(prog.scope)

    @staticmethod
    def _read_first_order_structure(struct: FirstOrderStructure) -> Tuple[
            List[syntax.SortedVar], # vs
            Dict[SortDecl, List[Expr]], # ineqs
            Dict[RelationDecl, List[Expr]], # rels
            Dict[ConstantDecl, Expr], # consts
            Dict[FunctionDecl, List[Expr]], # funcs
    ]:
        vars_by_sort: Dict[SortDecl, List[syntax.SortedVar]] = {}
        ineqs: Dict[SortDecl, List[Expr]] = {}
        rels: Dict[RelationDecl, List[Expr]] = {}
        consts: Dict[ConstantDecl, Expr] = {}
        funcs: Dict[FunctionDecl, List[Expr]] = {}
        for sort in struct.univs:
            vars_by_sort[sort] = [syntax.SortedVar(v, syntax.UninterpretedSort(sort.name))
                                  for v in struct.univs[sort]]
            u = [syntax.Id(s) for s in struct.univs[sort]]
            ineqs[sort] = [syntax.Neq(a, b) for a, b in itertools.combinations(u, 2)]

        for R, l in struct.rel_interps.items():
            rels[R] = []
            for tup, ans in l.items():
                e: Expr
                if tup:
                    args: List[Expr] = []
                    for (col, col_sort) in zip(tup, R.arity):
                        assert isinstance(col_sort, syntax.UninterpretedSort)
                        assert col_sort.decl is not None
                        args.append(syntax.Id(col))
                    e = syntax.AppExpr(R.name, tuple(args))
                else:
                    e = syntax.Id(R.name)
                e = e if ans else syntax.Not(e)
                rels[R].append(e)
        for C, c in struct.const_interps.items():
            e = syntax.Eq(syntax.Id(C.name), syntax.Id(c))
            consts[C] = e
        for F, fl in struct.func_interps.items():
            funcs[F] = []
            for tup, res in fl.items():
                e = syntax.AppExpr(F.name, tuple(syntax.Id(col) for col in tup))
                e = syntax.Eq(e, syntax.Id(res))
                funcs[F].append(e)

        vs = list(itertools.chain(*(vs for vs in vars_by_sort.values())))

        return vs, ineqs, rels, consts, funcs


    def ineq_conjuncts(self) -> Iterable[Tuple[SortDecl, int, Expr]]:
        for s, l in self.ineqs.items():
            S = self.tombstones[s]
            if S is not None:
                for i, e in enumerate(l):
                    if i not in S:
                        yield s, i, e

    def rel_conjuncts(self) -> Iterable[Tuple[RelationDecl, int, Expr]]:
        for r, l in self.rels.items():
            S = self.tombstones[r]
            if S is not None:
                for i, e in enumerate(l):
                    if i not in S:
                        yield r, i, e

    def func_conjuncts(self) -> Iterable[Tuple[FunctionDecl, int, Expr]]:
        for f, l in self.funcs.items():
            S = self.tombstones[f]
            if S is not None:
                for i, e in enumerate(l):
                    if i not in S:
                        yield f, i, e

    def const_conjuncts(self) -> Iterable[Tuple[ConstantDecl, int, Expr]]:
        for c, e in self.consts.items():
            S = self.tombstones[c]
            if S is not None and 0 not in S:
                yield c, 0, e

    def const_subst(self) -> Dict[syntax.Id, syntax.Id]:
        ans = {}
        for c, e in self.consts.items():
            assert isinstance(e, syntax.BinaryExpr) and e.op == 'EQUAL' and \
                isinstance(e.arg1, syntax.Id) and isinstance(e.arg2, syntax.Id)
            ans[e.arg2] = e.arg1
        return ans

    def conjuncts(self) -> Iterable[Tuple[_RelevantDecl, int, Expr]]:
        for t1 in self.ineq_conjuncts():
            yield t1
        for t2 in self.rel_conjuncts():
            yield t2
        for t3 in self.const_conjuncts():
            yield t3
        for t4 in self.func_conjuncts():
            yield t4

    def simplify_consts(self) -> None:
        subst = self.const_subst()
        I: Dict[SortDecl, List[Expr]]
        R: Dict[RelationDecl, List[Expr]]
        C: Dict[ConstantDecl, Expr]
        F: Dict[FunctionDecl, List[Expr]]

        def apply_subst1(e: Expr) -> Expr:
            return syntax.subst_vars_simple(e, subst)

        def apply_subst(l: List[Expr]) -> List[Expr]:
            return [apply_subst1(e) for e in l]

        def is_trivial_eq(eq: Expr) -> bool:
            return isinstance(eq, syntax.BinaryExpr) and eq.op == 'EQUAL' and \
                eq.arg1 == eq.arg2

        I = OrderedDict((s, apply_subst(l)) for s, l in self.ineqs.items())
        R = OrderedDict((r, apply_subst(l)) for r, l in self.rels.items())
        C = OrderedDict((c, apply_subst1(e)) for c, e in self.consts.items())
        F = OrderedDict((f, apply_subst(l)) for f, l in self.funcs.items())

        self.ineqs = I
        self.rels = R
        self.consts = OrderedDict((c, e) for c, e in C.items() if not is_trivial_eq(e))
        self.funcs = F

        self.prune_unused_vars()

    def __str__(self) -> str:
        return 'exists %s.\n  %s' % (
            ', '.join(v.name for v in self.binder.vs),
            ' &\n  '.join(str(c) for _, _, c in self.conjuncts())
        )

    def _typecheck(self, scope: Scope) -> None:
        typechecker.pre_typecheck_binder(scope, self.binder)
        with scope.in_scope(self.binder, [v.sort for v in self.binder.vs]):
            with scope.n_states(1):
                for _, _, c in self.conjuncts():
                    typechecker.typecheck_expr(scope, c, syntax.BoolSort)
        typechecker.post_typecheck_binder(self.binder)

    def get_vs(self) -> Tuple[syntax.SortedVar, ...]:
        return self.binder.vs

    def to_z3(self, t: Z3Translator, new: bool = False) -> z3.ExprRef:
        # TODO: make this return Expr, not z3.ExprRef
        bs = t.bind(self.binder)
        with t.scope.in_scope(self.binder, bs):
            z3conjs = []
            self.trackers = []
            self.reverse_map: List[Tuple[_RelevantDecl, int]] = []
            i = 0
            for (d, j, c) in self.conjuncts():
                p = z3.Bool('p%d' % i)
                self.trackers.append(p)
                self.reverse_map.append((d, j))
                z3conjs.append(p == t.translate_expr(New(c) if new else c))
                i += 1
        if bs:
            return z3.Exists(bs, z3.And(*z3conjs))
        else:
            return z3.And(*z3conjs)

    def to_ast(self) -> Expr:
        e = syntax.And(*(c for _, _, c in self.conjuncts()))
        vs = self.binder.vs

        return syntax.Exists(vs, e)

    def minimize_from_core(self, core: Optional[Iterable[int]]) -> None:
        if core is None:
            return

        I: Dict[SortDecl, List[Expr]] = {}
        R: Dict[RelationDecl, List[Expr]] = {}
        C: Dict[ConstantDecl, Expr] = {}
        F: Dict[FunctionDecl, List[Expr]] = {}

        for i in core:
            d, j = self.reverse_map[i]
            if isinstance(d, SortDecl):
                if d not in I:
                    I[d] = []
                I[d].append(self.ineqs[d][j])
            elif isinstance(d, RelationDecl):
                if d not in R:
                    R[d] = []
                R[d].append(self.rels[d][j])
            elif isinstance(d, FunctionDecl):
                if d not in F:
                    F[d] = []
                F[d].append(self.funcs[d][j])

            else:
                assert isinstance(d, ConstantDecl)
                assert d not in C
                C[d] = self.consts[d]

        self.prune_unused_vars()

        self.ineqs = I
        self.rels = R
        self.consts = C
        self.funcs = F

    def remove_clause(self, d: _RelevantDecl, i: Union[int, Set[int], None] = None) -> None:
        if i is None:
            self.tombstones[d] = None
        elif isinstance(i, int):
            S = self.tombstones[d]
            assert S is not None
            assert i not in S
            S.add(i)
        else:
            S = self.tombstones[d]
            assert S is not None
            assert i & S == set()
            S |= i

    def prune_unused_vars(self) -> None:
        self.binder.vs = tuple(v for v in self.binder.vs
                               if any(v.name in syntax.free_ids(c) for _, _, c in self.conjuncts()))

    @contextmanager
    def without(self, d: _RelevantDecl, j: Union[int, Set[int], None] = None) -> Iterator[None]:
        S = self.tombstones[d]
        if j is None:
            self.tombstones[d] = None
            yield
            self.tombstones[d] = S
        elif isinstance(j, int):
            assert S is not None
            assert j not in S
            S.add(j)
            yield
            S.remove(j)
        else:
            assert S is not None
            assert S & j == set()
            S |= j
            yield
            S -= j

    def generalize(self, s: Solver, constraint: Callable[[Diagram], bool], order: Optional[int] = None) -> None:
        'drop conjuncts of this diagram subject to the constraint returning true'
        d: _RelevantDecl
        I: Iterable[_RelevantDecl] = self.ineqs
        R: Iterable[_RelevantDecl] = self.rels
        C: Iterable[_RelevantDecl] = self.consts
        F: Iterable[_RelevantDecl] = self.funcs

        assert constraint(self)

        generalization_order = list(itertools.chain(I, R, C, F))
        generalization_order = reorder(generalization_order, order)

        for d in generalization_order:
            if isinstance(d, SortDecl) and len(self.ineqs[d]) == 1:
                continue
            with self.without(d):
                res = constraint(self)
            if res:
                self.remove_clause(d)
                continue
            if isinstance(d, RelationDecl):
                l = self.rels[d]
                cs = set()
                S = self.tombstones[d]
                assert S is not None
                for j, x in enumerate(l):
                    if j not in S and isinstance(x, syntax.UnaryExpr):
                        cs.add(j)
                with self.without(d, cs):
                    res = constraint(self)
                if res:
                    self.remove_clause(d, cs)

        for d, j, c in self.conjuncts():
            with self.without(d, j):
                res = constraint(self)
            if res:
                self.remove_clause(d, j)

        self.prune_unused_vars()

def reorder(lst: List[Union[SortDecl, RelationDecl, ConstantDecl, FunctionDecl]], order: Optional[int]) \
        -> List[Union[SortDecl, RelationDecl, ConstantDecl, FunctionDecl]]:
    if not order:
        return lst

    if order == -1:
        random.shuffle(lst)
        return lst

    assert 0 <= order < math.factorial(len(lst))
    return list(utils.generator_element(itertools.permutations(lst), order))
