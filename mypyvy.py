#!/usr/bin/env python3

from __future__ import annotations
import argparse
from collections import OrderedDict, defaultdict
from contextlib import contextmanager
import copy
from datetime import datetime
import functools
import io
import itertools
import logging
import networkx  # type: ignore
import sys
from typing import List, Any, Optional, Callable, Set, Tuple, Union, Iterable, \
    Dict, TypeVar, Sequence, overload, Generic, Iterator, cast
import xml
import xml.sax
import xml.sax.saxutils
import z3

import parser
import syntax
from syntax import Expr, Program, Scope, ConstantDecl, RelationDecl, SortDecl, \
    FunctionDecl, TransitionDecl, InvariantDecl, AutomatonDecl
from utils import MySet, OrderedSet

from phases import PhaseAutomaton, Phase, Frame, PhaseTransition

ALWAYS_PRINT = 35

class MyLogger(object):
    def __init__(self, logger: logging.Logger) -> None:
        self.logger = logger

    def setLevel(self, lvl: int) -> None:
        self.logger.setLevel(lvl)

    def isEnabledFor(self, lvl: int) -> bool:
        return self.logger.isEnabledFor(lvl)

    def warning(self, msg: str) -> None:
        self.log(logging.WARNING, msg)

    def info(self, msg: str) -> None:
        self.log(logging.INFO, msg)

    def debug(self, msg: str) -> None:
        self.log(logging.DEBUG, msg)

    def always_print(self, msg: str) -> None:
        self.log(ALWAYS_PRINT, msg)

    def log_list(self, lvl: int, msgs: List[str]) -> None:
        if args.log_xml:
            for msg in msgs:
                self.log(lvl, msg)
        else:
            self.log(lvl, '\n'.join(msgs))

    def log(self, lvl: int, msg: str) -> None:

        if self.isEnabledFor(lvl):
            if args.log_xml:
                msg = xml.sax.saxutils.escape(msg)
                with LogTag('msg', lvl=lvl, time=str((datetime.now() - start).total_seconds())):
                    self.rawlog(ALWAYS_PRINT, msg)
            else:
                self.rawlog(lvl, msg)

    def rawlog(self, lvl: int, msg: str) -> None:
        self.logger.log(lvl, msg)

logger = MyLogger(logging.getLogger(__file__))

class LogTag(object):
    def __init__(self, name: str, lvl: int=ALWAYS_PRINT, **kwargs: str) -> None:
        self.name = name
        self.lvl = lvl
        self.kwargs = kwargs

    def __enter__(self) -> None:
        if args.log_xml and logger.isEnabledFor(self.lvl):
            msg = ''
            for k, v in self.kwargs.items():
                msg += ' %s="%s"' % (k, xml.sax.saxutils.escape(v))

            logger.rawlog(ALWAYS_PRINT, '<%s%s>' % (self.name, msg))

    def __exit__(self, exn_type: Any, exn_value: Any, traceback: Any) -> None:
        if args.log_xml and logger.isEnabledFor(self.lvl):
            logger.rawlog(ALWAYS_PRINT, '</%s>' % self.name)


FuncType = Callable[..., Any]
F = TypeVar('F', bound=FuncType)
def log_start_end_time(lvl: int=logging.DEBUG) -> Callable[[F], F]:
    def dec(func: F) -> F:
        @functools.wraps(func)
        def wrapped(*args, **kwargs): # type: ignore
            start = datetime.now()
            logger.log(lvl, '%s started at %s' % (func.__name__, start))
            ans = func(*args, **kwargs)
            end = datetime.now()
            logger.log(lvl, '%s ended at %s (took %s seconds)' % (func.__name__, end, (end - start).total_seconds()))
            return ans
        return cast(F, wrapped)
    return dec

def log_start_end_xml(lvl: int=logging.DEBUG, tag: Optional[str]=None) -> Callable[[F], F]:
    def dec(func: F) -> F:
        @functools.wraps(func)
        def wrapped(*args, **kwargs): # type: ignore
            with LogTag(tag if tag is not None else func.__name__, lvl=lvl):
                ans = func(*args, **kwargs)
            return ans
        return cast(F, wrapped)
    return dec

z3.Forall = z3.ForAll

args: argparse.Namespace

KEY_ONE = 'one'
KEY_NEW = 'new'
KEY_OLD = 'old'

class Solver(object):
    def __init__(self, scope: Scope[z3.ExprRef]) -> None:
        self.z3solver = z3.Solver()
        self.scope = scope
        self.translators: Dict[Tuple[Optional[str], Optional[str]], syntax.Z3Translator] = {}
        self.nqueries = 0
        self.assumptions_necessary = False

    def get_translator(self, key: Optional[str]=None, key_old: Optional[str]=None) \
        -> syntax.Z3Translator:
        t = (key, key_old)
        if t not in self.translators:
            self.translators[t] = syntax.Z3Translator(self.scope, key, key_old)
        return self.translators[t]

    @contextmanager
    def mark_assumptions_necessary(self) -> Iterator[None]:
        old = self.assumptions_necessary
        self.assumptions_necessary = True
        yield None
        self.assumptions_necessary = old

    def __enter__(self) -> None:
        self.z3solver.push()

    def __exit__(self, exn_type: Any, exn_value: Any, traceback: Any) -> None:
        self.z3solver.pop()

    def add(self, e: z3.ExprRef) -> None:
        # if logger.isEnabledFor(logging.DEBUG):
        #     logger.debug('adding %s' % e)

        self.z3solver.add(e)

    def check(self, assumptions: Optional[Sequence[z3.ExprRef]]=None) -> z3.CheckSatResult:
        # logger.debug('solver.check')
        if assumptions is None:
            assert not self.assumptions_necessary
            assumptions = []
        self.nqueries += 1
        return self.z3solver.check(*assumptions)

    def model(self, assumptions: Optional[Sequence[z3.ExprRef]]=None) -> z3.ModelRef:
        if args.minimize_models:
            return self._minimal_model(assumptions)
        else:
            return self.z3solver.model()

    def _cardinality_constraint(self, s: z3.SortRef, n: int) -> z3.ExprRef:
        x = z3.Const('x', s)
        disjs = []
        for i in range(n):
            c = z3.Const('card_%s_%s' % (s.name(), i), s)
            disjs.append(x == c)

        return z3.Forall(x, z3.Or(*disjs))

    def _minimal_model(self, assumptions: Optional[Sequence[z3.ExprRef]]) -> z3.ModelRef:
        m = self.z3solver.model()
        # logger.debug('computing minimal model from initial model')
        # logger.debug(str(Model(prog, m, KEY_NEW, KEY_OLD)))
        # logger.debug('assertions')
        # logger.debug(str(self.assertions()))

        with self:
            for s in m.sorts():
                u = m.get_universe(s)
                n = 1
                while n < len(u):
                    with self:
                        self.add(self._cardinality_constraint(s, n))
                        res = self.check(assumptions)
                        if res == z3.sat:
                            break
                    n += 1
                if n < len(u):
                    self.add(self._cardinality_constraint(s, n))
            assert self.check(assumptions) == z3.sat
            m = self.z3solver.model()
            # logger.debug('finished with minimal model')
            # logger.debug(str(Model(prog, m, KEY_NEW, KEY_OLD)))
            return m

    def assertions(self) -> Sequence[z3.ExprRef]:
        l = self.z3solver.assertions()
        return sorted(l, key=lambda x: str(x))

    def unsat_core(self) -> Sequence[z3.ExprRef]:
        return self.z3solver.unsat_core()


T = TypeVar('T')

def check_unsat(
        toks: List[Optional[syntax.Token]],
        errmsgs: List[str],
        s: Solver,
        prog: Program,
        key: str,
        key_old: Optional[str]=None
) -> None:
    start = datetime.now()
    # if logger.isEnabledFor(logging.DEBUG):
    #     logger.debug('assertions')
    #     logger.debug(str(s.assertions()))

    if s.check() != z3.unsat:
        m = Model(prog, s.model(), key, key_old)

        logger.always_print('')
        logger.always_print(str(m))
        for tok, msg in zip(toks, errmsgs):
            syntax.print_error(tok, msg)
    logger.always_print('    ok. (%s)' % (datetime.now() - start))
    sys.stdout.flush()

@log_start_end_xml(logging.INFO)
def check_init(s: Solver, prog: Program) -> None:
    logger.always_print('checking init:')

    t = s.get_translator(KEY_ONE)

    with s:
        for init in prog.inits():
            s.add(t.translate_expr(init.expr))

        for inv in prog.invs():
            with s:
                s.add(z3.Not(t.translate_expr(inv.expr)))

                if inv.name is not None:
                    msg = ' ' + inv.name
                elif inv.tok is not None:
                    msg = ' on line %d' % inv.tok.lineno
                else:
                    msg = ''
                logger.always_print('  implies invariant%s...' % msg)
                sys.stdout.flush()

                check_unsat([inv.tok], ['invariant%s may not hold in initial state' % msg], s, prog, KEY_ONE)


def check_transitions(s: Solver, prog: Program) -> None:
    t = s.get_translator(KEY_NEW, KEY_OLD)

    with s:
        for inv in prog.invs():
            s.add(t.translate_expr(inv.expr, old=True))

        for trans in prog.transitions():
            logger.always_print('checking transation %s:' % (trans.name,))

            with s:
                s.add(t.translate_transition(trans))
                for inv in prog.invs():
                    with s:
                        s.add(z3.Not(t.translate_expr(inv.expr)))

                        if inv.name is not None:
                            msg = ' ' + inv.name
                        elif inv.tok is not None:
                            msg = ' on line %d' % inv.tok.lineno
                        else:
                            msg = ''
                        logger.always_print('  preserves invariant%s...' % msg)
                        sys.stdout.flush()

                        check_unsat([inv.tok, trans.tok],
                                    ['invariant%s may not be preserved by transition %s' %
                                     (msg, trans.name),
                                     'this transition may not preserve invariant%s' % (msg,)],
                                    s, prog, KEY_NEW, KEY_OLD)

def check_implication(
        s: Solver,
        hyps: Iterable[Expr],
        concs: Iterable[Expr]
) -> Optional[z3.ModelRef]:
    t = s.get_translator(KEY_ONE)
    with s:
        for e in hyps:
            s.add(t.translate_expr(e))
        for e in concs:
            with s:
                s.add(z3.Not(t.translate_expr(e)))
                # if logger.isEnabledFor(logging.DEBUG):
                #     logger.debug('assertions')
                #     logger.debug(str(s.assertions()))

                if s.check() != z3.unsat:
                    return s.model()

    return None

def check_two_state_implication_all_transitions(
        s: Solver,
        prog: Program,
        old_hyps: Iterable[Expr],
        new_conc: Expr
) -> Optional[Tuple[z3.ModelRef, TransitionDecl]]:
    t = s.get_translator(KEY_NEW, KEY_OLD)
    with s:
        for h in old_hyps:
            s.add(t.translate_expr(h, old=True))

        s.add(z3.Not(t.translate_expr(new_conc)))

        for trans in prog.transitions():
            with s:
                s.add(t.translate_transition(trans))

                # if logger.isEnabledFor(logging.DEBUG):
                #     logger.debug('assertions')
                #     logger.debug(str(s.assertions()))

                if s.check() != z3.unsat:
                    return s.model(), trans

    return None

def check_two_state_implication_along_transitions(
        s: Solver,
        prog: Program,
        old_hyps: Iterable[Expr],
        transitions: Sequence[PhaseTransition],
        new_conc: Expr
) -> Optional[Tuple[z3.ModelRef, PhaseTransition]]:
    t = s.get_translator(KEY_NEW, KEY_OLD)
    with s:
        for h in old_hyps:
            s.add(t.translate_expr(h, old=True))

        s.add(z3.Not(t.translate_expr(new_conc)))

        for phase_transition in transitions:
            #logger.debug("two state implication check post %s; transition %s; pre %s" % (new_conc, phase_transition, old_hyps))
            delta = phase_transition.transition_decl()
            trans = prog.scope.get_transition(delta.transition)
            assert trans is not None
            precond = delta.precond

            with s:
                s.add(t.translate_transition(trans, precond=precond))

                # if logger.isEnabledFor(logging.DEBUG):
                #     logger.debug('assertions')
                #     logger.debug(str(s.assertions()))

                if s.check() != z3.unsat:
                    #logger.debug("two state implication check invalid")
                    return s.model(), phase_transition
            #logger.debug("two state implication check valid")

    return None

class Diagram(object):
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
            vs: List[syntax.SortedVar],
            ineqs: Dict[SortDecl, List[Expr]],
            rels: Dict[RelationDecl, List[Expr]],
            consts: Dict[ConstantDecl, Expr],
            funcs: Dict[FunctionDecl, List[Expr]]
    ) -> None:
        self.binder = syntax.Binder(vs)
        self.ineqs = ineqs
        self.rels = rels
        self.consts = consts
        self.funcs = funcs
        self.trackers: List[z3.ExprRef] = []
        self.tombstones: Dict[Union[SortDecl, RelationDecl, ConstantDecl, FunctionDecl], Union[Set[int], None]] = \
            defaultdict(lambda: set())

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

    def conjuncts(self) -> Iterable[Tuple[Union[SortDecl, RelationDecl, ConstantDecl, FunctionDecl], int, Expr]]:
        for t1 in self.ineq_conjuncts():
            yield t1
        for t2 in self.rel_conjuncts():
            yield t2
        for t3 in self.const_conjuncts():
            yield t3
        for t4 in self.func_conjuncts():
            yield t4

    def conjuncts_simple(self) -> Iterable[Tuple[Union[SortDecl, RelationDecl, ConstantDecl, FunctionDecl], int, Expr]]:
        subst = self.const_subst()
        s: Union[SortDecl, RelationDecl, FunctionDecl]
        for (s, r, e) in self.ineq_conjuncts():
            yield (s, r, syntax.subst_vars_simple(e, subst))
        for (s, r, e) in self.rel_conjuncts():
            yield (s, r, syntax.subst_vars_simple(e, subst))
        for (s, r, e) in self.func_conjuncts():
            yield (s, r, syntax.subst_vars_simple(e, subst))

    def simplify_consts(self) -> None:
        subst = self.const_subst()
        I: Dict[SortDecl, List[Expr]]
        R: Dict[RelationDecl, List[Expr]]
        C: Dict[ConstantDecl, Expr]
        F: Dict[FunctionDecl, List[Expr]]

        def apply_subst1(e: Expr) -> Expr: return syntax.subst_vars_simple(e, subst)
        def apply_subst(l: List[Expr]) -> List[Expr]: return [apply_subst1(e) for e in l]
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

    def resolve(self, scope: Scope) -> None:
        self.binder.pre_resolve(scope)

        with scope.in_scope(self.binder, [v.sort for v in self.binder.vs]):
            for _, _, c in self.conjuncts():
                c.resolve(scope, syntax.BoolSort)

        self.binder.post_resolve()

    def to_z3(self, t: syntax.Z3Translator) -> z3.ExprRef:
        bs = t.bind(self.binder)
        with t.scope.in_scope(self.binder, bs):
            z3conjs = []
            self.trackers = []
            self.reverse_map: List[Tuple[Union[SortDecl, RelationDecl, ConstantDecl, FunctionDecl], int]] = []
            i = 0

            for (d, j, c) in self.conjuncts():
                p = z3.Bool('p%d' % i)
                self.trackers.append(p)
                self.reverse_map.append((d, j))
                z3conjs.append(p == t.translate_expr(c))
                i += 1

        if len(bs) > 0:
            return z3.Exists(bs, z3.And(*z3conjs))
        else:
            return z3.And(*z3conjs)

    def to_ast(self) -> Expr:
        # TODO: remove this option on merge
        if args.simple_conjuncts:
            e = syntax.And(*(c for _, _, c in self.conjuncts_simple()))
            fv = e.free_ids()
            vs = [v for v in self.binder.vs if v.name in fv]
        else:
            e = syntax.And(*(c for _, _, c in self.conjuncts()))
            vs = self.binder.vs

        if len(vs) == 0:
            return e
        else:
            return syntax.Exists(vs, e)

    # TODO: can be removed? replaced with Frames.valid_in_initial_frame (YF)
    def valid_in_init(self, s: Solver, prog: Program) -> Optional[z3.ModelRef]:
        return check_implication(s, (init.expr for init in prog.inits()), [syntax.Not(self.to_ast())])

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

    def remove_clause(self, d: Union[SortDecl, RelationDecl, ConstantDecl, FunctionDecl], i: Union[int, Set[int], None]=None) -> None:
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
        self.binder.vs = [v for v in self.binder.vs
                          if any(v.name in c.free_ids() for _, _, c in self.conjuncts())]


    @contextmanager
    def without(self, d: Union[SortDecl, RelationDecl, ConstantDecl, FunctionDecl], j: Union[int, Set[int], None]=None) -> Iterator[None]:
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


    def smoke(self, s: Solver, prog: Program, depth: Optional[int]) -> None:
        if args.smoke_test and depth is not None:
            logger.debug('smoke testing at depth %s...' % (depth,))
            logger.debug(str(self))
            res = check_bmc(s, prog, syntax.Not(self.to_ast()), depth)
            if res is not None:
                logger.debug('no!')
                verbose_print_z3_model(res)
            logger.debug('ok.')

    # TODO: merge similarities with clause_implied_by_transitions_from_frame...
    def check_valid_in_phase_from_frame(self, s: Solver, prog: Program, f: Frame,
                                        transitions_to_grouped_by_src: Dict[Phase, Sequence[PhaseTransition]],
                                        propagate_init: bool) \
    -> Optional[z3.ModelRef]:
        for src, transitions in transitions_to_grouped_by_src.items():
            # logger.debug("gen: check transition from %s by %s" % (src.name(), str(list(transitions))))
            ans = check_two_state_implication_along_transitions(s, prog, f.summary_of(src), transitions,
                                                                syntax.Not(self.to_ast()))
            if ans is not None:
                return ans[0]

        if propagate_init:
            return self.valid_in_init(s, prog)
        return None

    @log_start_end_xml()
    @log_start_end_time()
    def generalize(self, s: Solver, prog: Program, f: Frame,
                   transitions_to_grouped_by_src: Dict[Phase, Sequence[PhaseTransition]],
                   propagate_init: bool,
                   depth: Optional[int]=None) -> None:
        if logger.isEnabledFor(logging.DEBUG):
            logger.debug('generalizing diagram')
            logger.debug(str(self))
            with LogTag('previous-frame', lvl=logging.DEBUG):
                for p in f.phases():
                    logger.log_list(logging.DEBUG, ['previous frame for %s is' % p.name()] + [str(x) for x in f.summary_of(p)])

        T = Union[SortDecl, RelationDecl, ConstantDecl, FunctionDecl]
        d: T
        I: Iterable[T] = self.ineqs
        R: Iterable[T] = self.rels
        C: Iterable[T] = self.consts
        F: Iterable[T] = self.funcs

#         if logger.isEnabledFor(logging.DEBUG):
#             logger.debug('checking that transition relation itself is SAT from previous frame...')
#             res1 = check_two_state_implication_all_transitions(s, prog, f, syntax.Bool(None, False))
#             if res1 is None:
#                 assert False
#             m, t = res1
#             logger.always_print(str(m))
#             logger.always_print(t.name)

        self.smoke(s, prog, depth)

        with LogTag('eliminating-conjuncts', lvl=logging.DEBUG):
            for d in itertools.chain(I, R, C, F):
                if isinstance(d, SortDecl) and len(self.ineqs[d]) == 1:
                    continue
                with self.without(d):
                    res = self.check_valid_in_phase_from_frame(s, prog, f, transitions_to_grouped_by_src, propagate_init)
                if res is None:
                    if logger.isEnabledFor(logging.DEBUG):
                        logger.debug('eliminated all conjuncts from declaration %s' % d)
                    self.remove_clause(d)
                    self.smoke(s, prog, depth)
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
                        res = self.check_valid_in_phase_from_frame(s, prog, f, transitions_to_grouped_by_src, propagate_init)
                    if res is None:
                        if logger.isEnabledFor(logging.DEBUG):
                            logger.debug('eliminated all negative conjuncts from declaration %s' % d)
                        self.remove_clause(d, cs)
                        self.smoke(s, prog, depth)

            for d, j, c in self.conjuncts():
                with self.without(d, j):
                    res = self.check_valid_in_phase_from_frame(s, prog, f, transitions_to_grouped_by_src, propagate_init)
                if res is None:
                    if logger.isEnabledFor(logging.DEBUG):
                        logger.debug('eliminated clause %s' % c)
                    self.remove_clause(d, j)
                    self.smoke(s, prog, depth)
    #            elif logger.isEnabledFor(logging.DEBUG):
    #
    #                logger.debug('failed to eliminate clause %s' % c)
    #                logger.debug('from diagram %s' % self)
    #
    #                if isinstance(res, tuple):
    #                    m, t = res
    #                    logger.debug('because of transition %s' % t.name)
    #                    logger.debug('and model %s' % Model(prog, m, KEY_NEW, KEY_OLD))
    #                else:
    #                    logger.debug('because the diagram is satisfiable in the initial state')
    #                    logger.debug('and model %s' % Model(prog, m, KEY_ONE))



        self.prune_unused_vars()

        if logger.isEnabledFor(logging.DEBUG):
            logger.debug('generalized diag')
            logger.debug(str(self))

def log_diagram(diag: Diagram, lvl: int=logging.DEBUG) -> None:
    logger.log(lvl, str(diag))

class Model(object):
    def __init__(
            self,
            prog: Program,
            m: z3.ModelRef,
            key: str,
            key_old: Optional[str]=None
    ) -> None:
        self.prog = prog
        self.z3model = m
        self.key = key
        self.key_old = key_old

        self.read_out()

    def univ_str(self) -> List[str]:
        l = []
        for s in sorted(self.univs.keys(), key=str):
            l.append(str(s))
            for x in self.univs[s]:
                l.append('  %s' % x)
        return l

    def __str__(self) -> str:
        l = []
        l.extend(self.univ_str())
        l.append(Model._state_str(self.immut_const_interps, self.immut_rel_interps, self.immut_func_interps))
        if self.key_old is not None:
            l.append('\nold state:')
            l.append(Model._state_str(self.old_const_interps, self.old_rel_interps, self.old_func_interps))
            l.append('\nnew state:')
        else:
            l.append('')
        l.append(Model._state_str(self.const_interps, self.rel_interps, self.func_interps))

        return '\n'.join(l)

    @staticmethod
    def _state_str(
            Cs: Dict[ConstantDecl,str],
            Rs: Dict[RelationDecl, List[Tuple[List[str], bool]]],
            Fs: Dict[FunctionDecl, List[Tuple[List[str], str]]]
    ) -> str:
        l = []
        for C in Cs:
            l.append('%s = %s' % (C.name, Cs[C]))

        for R in Rs:
            for tup, b in sorted(Rs[R]):
                l.append('%s%s(%s)' % ('' if b else '!', R.name, ','.join(tup)))

        for F in Fs:
            for tup, res in sorted(Fs[F]):
                l.append('%s(%s) = %s' % (F.name, ','.join(tup), res))


        return '\n'.join(l)

    def read_out(self) -> None:
        # logger.debug('read_out')
        def rename(s: str) -> str:
            return s.replace('!val!', '')

        self.univs: Dict[SortDecl, List[str]] = OrderedDict()
        for z3sort in sorted(self.z3model.sorts(), key=str):
            sort = self.prog.scope.get_sort(str(z3sort))
            assert sort is not None
            self.univs[sort] = list(sorted(rename(str(x)) for x in self.z3model.get_universe(z3sort)))
            # if logger.isEnabledFor(logging.DEBUG):
            #     logger.debug(str(z3sort))
            #     for x in self.univs[sort]:
            #         logger.debug('  ' + x)


        RT = Dict[RelationDecl, List[Tuple[List[str], bool]]]
        CT = Dict[ConstantDecl, str]
        FT = Dict[FunctionDecl, List[Tuple[List[str], str]]]

        self.immut_rel_interps: RT = OrderedDict()
        self.immut_const_interps: CT = OrderedDict()
        self.immut_func_interps: FT = OrderedDict()

        self.rel_interps: RT = OrderedDict()
        self.const_interps: CT = OrderedDict()
        self.func_interps: FT = OrderedDict()

        if self.key_old is not None:
            self.old_rel_interps: RT = OrderedDict()
            self.old_const_interps: CT = OrderedDict()
            self.old_func_interps: FT = OrderedDict()

        for z3decl in sorted(self.z3model.decls(), key=str):
            z3name = str(z3decl)
            if z3name.startswith(self.key):
                name = z3name[len(self.key)+1:]
                R: RT = self.rel_interps
                C: CT = self.const_interps
                F: FT = self.func_interps
            elif self.key_old is not None and z3name.startswith(self.key_old):
                name = z3name[len(self.key_old)+1:]
                R = self.old_rel_interps
                C = self.old_const_interps
                F = self.old_func_interps
            else:
                name = z3name
                R = self.immut_rel_interps
                C = self.immut_const_interps
                F = self.immut_func_interps


            decl = self.prog.scope.get(name)
            assert not isinstance(decl, syntax.Sort) and \
                not isinstance(decl, syntax.SortInferencePlaceholder)
            if decl is not None:
#                if logger.isEnabledFor(logging.DEBUG):
#                    logger.debug(str(z3decl))
                if isinstance(decl, RelationDecl):
                    if len(decl.arity) > 0:
                        rl = []
                        domains = [self.z3model.get_universe(z3decl.domain(i))
                                   for i in range(z3decl.arity())]
                        g = itertools.product(*domains)
                        for row in g:
                            ans = self.z3model.eval(z3decl(*row))
                            rl.append(([rename(str(col)) for col in row], bool(ans)))
                        assert decl not in R
                        R[decl] = rl
                    else:
                        ans = self.z3model.eval(z3decl())
                        assert decl not in R
                        R[decl] = [([], bool(ans))]
                elif isinstance(decl, FunctionDecl):
                    fl = []
                    domains = [self.z3model.get_universe(z3decl.domain(i))
                               for i in range(z3decl.arity())]
                    g = itertools.product(*domains)
                    for row in g:
                        ans = self.z3model.eval(z3decl(*row))
                        fl.append(([rename(str(col)) for col in row], rename(ans.decl().name())))
                    assert decl not in F
                    F[decl] = fl

                else:
                    assert isinstance(decl, ConstantDecl)
                    v = self.z3model.eval(z3decl()).decl().name()
                    assert decl not in C
                    C[decl] = rename(v)
            else:
                pass
#                 if logger.isEnabledFor(logging.DEBUG):
#                     logger.debug('extra constant: ' + str(z3decl))

    def as_diagram(self, old: Optional[bool]=None) -> Diagram:
        assert self.key_old is None or old is not None, 'to generate a diagram from a 2-state model, you must specify whether you want the pre-diagram or the post-diagram'
        assert old is None or self.key_old is not None, 'specifying pre- or post- diagram makes no sense in a 1-state model'

        if old:
            mut_rel_interps = self.old_rel_interps
            mut_const_interps = self.old_const_interps
            mut_func_interps = self.old_func_interps
        else:
            mut_rel_interps = self.rel_interps
            mut_const_interps = self.const_interps
            mut_func_interps = self.func_interps

        vs: List[syntax.SortedVar] = []
        ineqs: Dict[SortDecl, List[Expr]] = OrderedDict()
        rels: Dict[RelationDecl, List[Expr]] = OrderedDict()
        consts: Dict[ConstantDecl, Expr] = OrderedDict()
        funcs: Dict[FunctionDecl, List[Expr]] = OrderedDict()
        for sort in self.univs:
            vs.extend(syntax.SortedVar(None, v, syntax.UninterpretedSort(None, sort.name))
                      for v in self.univs[sort])

            ineqs[sort] = []
            u = [syntax.Id(None, s) for s in self.univs[sort]]
            for i, a in enumerate(u):
                for b in u[i+1:]:
                    ineqs[sort].append(syntax.Neq(a, b))
        for R, l in itertools.chain(mut_rel_interps.items(), self.immut_rel_interps.items()):
            rels[R] = []
            for tup, ans in l:
                e: Expr
                if len(tup) > 0:
                    e = syntax.AppExpr(None, R.name, [syntax.Id(None, col) for col in tup])

                else:
                    e = syntax.Id(None, R.name)
                e = e if ans else syntax.Not(e)
                rels[R].append(e)
        for C, c in itertools.chain(mut_const_interps.items(), self.immut_const_interps.items()):
            e = syntax.Eq(syntax.Id(None, C.name), syntax.Id(None, c))
            consts[C] = e
        for F, fl in itertools.chain(mut_func_interps.items(), self.immut_func_interps.items()):
            funcs[F] = []
            for tup, res in fl:
                e = syntax.AppExpr(None, F.name, [syntax.Id(None, col) for col in tup])
                e = syntax.Eq(e, syntax.Id(None, res))
                funcs[F].append(e)


        diag = Diagram(vs, ineqs, rels, consts, funcs)
        if args.simplify_diagram:
            diag.simplify_consts()
        assert self.prog.scope is not None
        diag.resolve(self.prog.scope)

        return diag

class Blocked(object):
    pass
class CexFound(object):
    pass
class GaveUp(object):
    pass

def verbose_print_z3_model(m: z3.ModelRef) -> None:
    logger.always_print('')
    out = io.StringIO()
    fmt = z3.Formatter() # type: ignore
    fmt.max_args = 10000
    logger.always_print(str(fmt.max_args))
    pp = z3.PP() # type: ignore
    pp.max_lines = 10000
    pp(out, fmt(m))
    logger.always_print(out.getvalue())
    assert False



class Frames(object):
    @log_start_end_xml(logging.DEBUG, 'Frames.__init__')
    def __init__(self, solver: Solver, prog: Program, automaton: Optional[AutomatonDecl]=None) -> None:
        self.solver = solver
        self.prog = prog

        if automaton is None:
            if args.safety is None:
                syntax.error(None, 'updr without --automaton requires --safety')
            the_phase = 'the_phase'
            pcs = []
            for t in self.prog.transitions():
                pcs.append(syntax.PhaseTransitionDecl(None, t.name, None, the_phase))
            automaton = AutomatonDecl(None, [syntax.SafetyDecl(None, args.safety),
                                             syntax.InitPhaseDecl(None, the_phase),
                                             syntax.PhaseDecl(None, the_phase, pcs)])

            print(automaton)

        l = []
        for s in automaton.safeties():
            inv = prog.scope.get_invariant(s.name)
            assert inv is not None
            l.append(inv.expr)
        self.safety = l

        self.automaton = PhaseAutomaton(automaton)
        self.fs: List[Frame] = []
        self.push_cache: List[Dict[Phase, Set[Expr]]] = []
        self.counter = 0

        init_conjuncts = [init.expr for init in prog.inits()]
        self.new_frame({p: init_conjuncts if p == self.automaton.init_phase()
                            else [syntax.FalseExpr]
                        for p in self.automaton.phases()})

        self.new_frame()

    def __getitem__(self, i: int) -> Frame:
        return self.fs[i]

    def __setitem__(self, i: int, e: Frame) -> None:
        assert e is self.fs[i]

    def __len__(self) -> int:
        return len(self.fs)

    def _fresh_solver(self) -> Solver:
        scope = self.prog.scope
        assert scope is not None
        assert len(scope.stack) == 0

        return Solver(cast(Scope[z3.ExprRef], scope))

    def new_frame(self, contents: Optional[Dict[Phase, Sequence[Expr]]]=None) -> None:
        if contents is None:
            contents = {}
        logger.debug("new frame! %s" % len(self.fs))
        self.fs.append(Frame(self.automaton.phases(), contents))
        self.push_cache.append({p: set() for p in self.automaton.phases()})

        self.push_forward_frames()

        with LogTag('current-frames-after-push', lvl=logging.DEBUG):
            self.print_frames(lvl=logging.DEBUG)

        self.establish_safety()

        with LogTag('current-frames-after-safety', lvl=logging.DEBUG):
            self.print_frames(lvl=logging.DEBUG)

        self.simplify()

        with LogTag('current-frames-after-simplify', lvl=logging.DEBUG):
            self.print_frames(lvl=logging.DEBUG)



    @log_start_end_xml()
    def establish_safety(self) -> None:
        self.assert_inductive_trace()

        frame_no = len(self.fs) - 1
        f = self.fs[-1]

        while True:
            with LogTag('establish-safety-attempt'):
                res = self._get_some_cex_to_safety()

                if res is None:
                    return

                (violating, diag) = res
                self.block(diag, frame_no, violating, [(None, diag)], True)

        self.assert_inductive_trace()

    def _get_some_cex_to_safety(self) -> Optional[Tuple[Phase, Diagram]]:
        f = self.fs[-1]

        def safety_property_checker(p: Phase) -> Optional[Tuple[Phase, Diagram]]:
            res = check_implication(self.solver, f.summary_of(p), self.safety)

            if res is None:
                logger.debug("Frontier frame phase %s implies safety, summary is %s" % (p.name(), f.summary_of(p)))
                return None

            logger.debug("Frontier frame phase %s cex to safety" % p.name())
            z3m: z3.ModelRef = res
            mod = Model(self.prog, z3m, KEY_ONE)
            diag = mod.as_diagram()
            return (p, diag)

        def edge_covering_checker(p: Phase) -> Optional[Tuple[Phase, Diagram]]:
            t = self.solver.get_translator(KEY_NEW, KEY_OLD)
            f = self.fs[-1]

            with self.solver:
                for c in f.summary_of(p):
                    self.solver.add(t.translate_expr(c, old=True))

                transitions_from_phase = self.automaton.transitions_from(p)

                for trans in self.prog.transitions():
                    edges_from_phase_matching_prog_trans = [t for t in transitions_from_phase
                                                                if t.prog_transition_name() == trans.name]
                    if any(delta.precond is None for delta in edges_from_phase_matching_prog_trans):
                        logger.debug('transition %s is covered trivially by %s' % (trans.name, p.name()))
                        continue

                    logger.debug('checking transition %s is covered by %s' % (trans.name, p.name()))

                    with self.solver:
                        self.solver.add(t.translate_transition(trans))
                        self.solver.add(z3.And(*(z3.Not(t.translate_precond_of_transition(delta.precond(), trans))
                                       for delta in edges_from_phase_matching_prog_trans)))

                        if self.solver.check() != z3.unsat:
                            logger.debug('phase %s cex to edge covering of transition %s' % (p.name(), trans.name))
                            z3m: z3.ModelRef = self.solver.model()
                            mod = Model(self.prog, z3m, KEY_NEW, KEY_OLD)
                            diag = mod.as_diagram(old=True)
                            return (p, diag)

                        logger.debug('transition %s is covered non-trivially by %s' % (trans.name, p.name()))
                        continue

                logger.debug('all edges covered from phase %s' % p.name())
                return None

        # TODO: also check edge covering
        safety_checkers = [safety_property_checker, edge_covering_checker]
        for p in self.automaton.phases():
            for checker in safety_checkers:
                sres = checker(p)
                if sres is not None:
                    return sres
        return None

    def get_inductive_frame(self) -> Optional[Frame]:
        for i in range(len(self) - 1):
            if self.is_frame_inductive(i):
                return self[i+1]
        return None

    def is_frame_inductive(self, i: int) -> bool:
        for p in self.automaton.phases():
            if check_implication(self.solver, self[i + 1].summary_of(p), self[i].summary_of(p)) is not None:
                return False
        return True

    def push_conjunct(self, frame_no: int, c: Expr, p: Phase, frame_old_count: Optional[int]=None) -> None:
        is_safety = c in self.safety
        conjunct_old_count = self.counter

        f = self.fs[frame_no]
        while True:
            with LogTag('pushing-conjunct-attempt', lvl=logging.DEBUG, frame=str(frame_no), conj=str(c)):
                logger.debug('frame %s phase %s attempting to push %s' % (frame_no, p.name(), c))

                res = self.clause_implied_by_transitions_from_frame(f, p, c)
                if res is None:
                    logger.debug('frame %s phase %s managed to push %s' % (frame_no, p.name(), c))

                    if args.smoke_test and logger.isEnabledFor(logging.DEBUG):
                        logger.debug('jrw smoke testing...')
                        # TODO: phases
                        om = check_bmc(self.solver, self.prog, c, frame_no + 1)
                        if om is not None:
                            logger.debug('no!')
                            verbose_print_z3_model(om)
                        logger.debug('ok.')

                    # assert self.clause_implied_by_transitions_from_frame(f, p, c) is None
                    self[frame_no + 1].strengthen(p, c)
                    self.assert_inductive_trace()
                    break

                pre_phase, (m, t) = res
                mod = Model(self.prog, m, KEY_NEW, KEY_OLD)
                diag = mod.as_diagram(old=True)

                if logger.isEnabledFor(logging.DEBUG):
                    logger.debug('frame %s failed to immediately push %s due to transition %s' % (frame_no, c, t.pp()))
                    # logger.debug(str(mod))
                if is_safety:
                    logger.debug('note: current clause is safety condition')
                    self.block(diag, frame_no, pre_phase, [(None, c), (t, diag)], safety_goal=True)
                else:
                    if not args.dont_block_may_cexs:
                        ans = self.block(diag, frame_no, pre_phase, [(None, c), (t, diag)], safety_goal=False)
                        if isinstance(ans, CexFound):
                            break
                    else:
                        break

    @log_start_end_xml(logging.DEBUG)
    def push_forward_frames(self) -> None:
        self.assert_inductive_trace()
        for i, f in enumerate(self.fs[:-1]):
            if i == 0:
                continue
            with LogTag('pushing-frame', lvl=logging.DEBUG, i=str(i)):
                for p in self.automaton.phases():
                    logger.debug('pushing in frame %d phase %s' % (i, p.name()))
                    self.push_phase_from_pred(i, f, p)
                    # self.assert_inductive_trace()

        self.assert_inductive_trace()

    def assert_inductive_trace(self) -> None:
        if not args.assert_inductive_trace:
            return

        for i, f in enumerate(self.fs[:-1]):
            with LogTag('inductive-trace-assert', lvl=logging.DEBUG, i=str(i)):
                for p in self.automaton.phases():
                    for c in self.fs[i+1].summary_of(p):
                        res = self.clause_implied_by_transitions_from_frame(f, p, c, self._fresh_solver())
                        assert res is None, "Non inductive trace:\n\t%s\n\t%s\n\t%s" % (p.name(), c, f)

    def push_phase_from_pred(self, i: int, f: Frame, p: Phase) -> None:
        frame_old_count = self.counter

        def process_conjunct(c: Expr) -> None:
            if c in self.fs[i+1].summary_of(p) or c in self.push_cache[i][p]:
                return

            with LogTag('pushing-conjunct', lvl=logging.DEBUG, frame=str(i), conj=str(c)):
                self.push_conjunct(i, c, p, frame_old_count)

            self.push_cache[i][p].add(c)

        conjuncts = f.summary_of(p)

        j = 0
        while j < len(conjuncts):
            c = conjuncts.l[j]
            process_conjunct(c)
            j += 1


    # Block the diagram in the given frame.
    # If safety_goal is True, the only possible outcomes are returning Blocked() on success
    # or throwing an exception describing an abstract counterexample on failure.
    # If safety_goal is False, then no abstract counterexample is ever reported to user,
    # instead, CexFound() is returned to indicate the diagram could not be blocked.
    @log_start_end_xml(lvl=logging.DEBUG)
    def block(
            self,
            diag: Diagram,
            j: int,
            p: Phase,
            trace: List[Tuple[Optional[PhaseTransition],Union[Diagram, Expr]]]=[],
            safety_goal: bool=True
    ) -> Union[Blocked, CexFound]:
        if j == 0 or (j == 1 and self.valid_in_initial_frame(self.solver, p, diag) is not None):
            if safety_goal:
                logger.always_print('\n'.join(((t.pp() + ' ') if t is not None else '') + str(diag) for t, diag in trace))
                raise Exception('abstract counterexample')
            else:
                if logger.isEnabledFor(logging.DEBUG):
                    logger.debug('failed to block diagram')
                    # logger.debug(str(diag))
                return CexFound()

        old_count = self.counter

        # print fs
        while True:
            if logger.isEnabledFor(logging.DEBUG):
                logger.debug('blocking diagram in frame %s' % j)
                log_diagram(diag, lvl=logging.DEBUG)

                self.print_frame(j-1, lvl=logging.DEBUG)
            res, x = self.find_predecessor(self[j-1], p, diag)
            if res == z3.unsat:
                logger.debug('no predecessor: blocked!')
                # assert self.clause_implied_by_transitions_from_frame(self[j-1], p, syntax.Not(diag.to_ast())) is None
                assert x is None or isinstance(x, MySet)
                core: Optional[MySet[int]] = x
                self.augment_core_for_init(p, diag, core)
                break
            assert isinstance(x, tuple), (res, x)
            trans, (pre_phase, pre_diag) = x

            trace.append((trans, pre_diag))
            ans = self.block(pre_diag, j-1, pre_phase, trace, safety_goal)
            if not isinstance(ans, Blocked):
                return ans
            trace.pop()

        if logger.isEnabledFor(logging.DEBUG) and core is not None:
            logger.debug('core %s' % core)
            logger.debug('unminimized diag\n%s' % diag)

        diag.minimize_from_core(core)
        diag.generalize(self.solver, self.prog,
                        self[j-1], self.automaton.transitions_to_grouped_by_src(p), p == self.automaton.init_phase(),
                        j)

        e = syntax.Not(diag.to_ast())

        if logger.isEnabledFor(logging.DEBUG):
            logger.debug('adding new clause to frames 0 through %d phase %s' % (j, p.name()))
        if logger.isEnabledFor(logging.INFO):
            logger.info("[%d] %s" % (j, str(e)))

        # assert self.clause_implied_by_transitions_from_frame(self.fs[j-1], p, syntax.Not(diag.to_ast())) is None
        self.add(p, e, j)
        logger.debug("Done blocking")

        return Blocked()

    def valid_in_initial_frame(self, s: Solver, p: Phase, diag: Diagram) -> Optional[z3.ModelRef]:
        return check_implication(s, self.fs[0].summary_of(p), [syntax.Not(diag.to_ast())])


    def augment_core_for_init(self, p: Phase, diag: Diagram, core: Optional[MySet[int]]) -> None:
        if core is None or not args.use_z3_unsat_cores:
            return

        t = self.solver.get_translator(KEY_ONE)

        with self.solver:
            for init in self.fs[0].summary_of(p):
                self.solver.add(t.translate_expr(init))

            self.solver.add(diag.to_z3(t))

            res = self.solver.check(diag.trackers)

            assert res == z3.unsat
            uc = self.solver.unsat_core()
            # if logger.isEnabledFor(logging.DEBUG):
            #     logger.debug('uc')
            #     logger.debug(str(sorted(uc, key=lambda y: y.decl().name())))

                # logger.debug('assertions')
                # logger.debug(str(self.solver.assertions()))

            res = self.solver.check([diag.trackers[i] for i in core])
            if res == z3.unsat:
                logger.debug('augment_core_for_init: existing core sufficient')
                return

            for x in sorted(uc, key=lambda y: y.decl().name()):
                assert isinstance(x, z3.ExprRef)
                core.add(int(x.decl().name()[1:]))
            if logger.isEnabledFor(logging.DEBUG):
                logger.debug('augment_core_for_init: new core')
                logger.debug(str(sorted(core)))

    def add(self, p: Phase, e: Expr, depth: Optional[int]=None) -> None:
        self.counter += 1

        if depth is None:
            depth = len(self)

        if args.smoke_test and logger.isEnabledFor(logging.DEBUG):
            logger.debug('smoke testing at depth %s...' % (depth,))
            res = check_bmc(self.solver, self.prog, e, depth)
            if res is not None:
                logger.debug('no!')
                verbose_print_z3_model(res)
            logger.debug('ok.')

        self.assert_inductive_trace()
        for i in range(depth+1):
            self[i].strengthen(p, e)
            logger.debug("%d %s %s" % (i, p.name(), e))
            self.assert_inductive_trace()
        self.assert_inductive_trace()

    @log_start_end_xml(lvl=logging.DEBUG)
    def find_predecessor(
            self,
            pre_frame: Frame,
            current_phase: Phase,
            diag: Diagram
    ) -> Tuple[z3.CheckSatResult, Union[Optional[MySet[int]], Tuple[PhaseTransition, Tuple[Phase, Diagram]]]]:
        t = self.solver.get_translator(KEY_NEW, KEY_OLD)

        if args.use_z3_unsat_cores:
            core: Optional[MySet[int]] = MySet()
        else:
            core = None

        with self.solver:
            with self.solver.mark_assumptions_necessary():
                self.solver.add(diag.to_z3(t))

                transitions_into = self.automaton.transitions_to_grouped_by_src(current_phase)
                for src in self._predecessor_precedence(current_phase, list(transitions_into.keys())):
                    transitions = transitions_into[src]
                    assert transitions
                    logger.debug("check predecessor of %s from %s by %s" % (current_phase.name(), src.name(), transitions))
                    (sat_res, pre_diag) = self.find_predecessor_from_src_phase(t, pre_frame, src, transitions, diag, core)
                    if sat_res == z3.unsat:
                        continue
                    return (sat_res, pre_diag)

                if args.use_z3_unsat_cores:
                    assert core is not None
                    ret_core: Optional[MySet[int]] = MySet(sorted(core))
                else:
                    ret_core = None

                # assert self.clause_implied_by_transitions_from_frame(pre_frame, current_phase, syntax.Not(diag.to_ast())) is None
                return (z3.unsat, ret_core)

    def _predecessor_precedence(self, dst_phase: Phase, pre_phases: Sequence[Phase]) -> Sequence[Phase]:
        if dst_phase not in pre_phases:
            return pre_phases
        return [x for x in pre_phases if x != dst_phase] + [dst_phase]

    def find_predecessor_from_src_phase(
            self,
            t: syntax.Z3Translator,
            pre_frame: Frame,
            src_phase: Phase,
            transitions: Sequence[PhaseTransition],
            diag: Diagram,
            core: Optional[MySet[int]]
    ) -> Tuple[z3.CheckSatResult, Optional[Tuple[PhaseTransition, Tuple[Phase, Diagram]]]]:

            solver = self.solver
            with solver:

                for f in pre_frame.summary_of(src_phase):
                    solver.add(t.translate_expr(f, old=True))

                for phase_transition in transitions:
                    delta = phase_transition.transition_decl()
                    trans = self.prog.scope.get_transition(delta.transition)
                    assert trans is not None
                    precond = delta.precond

                    with solver:
                        solver.add(t.translate_transition(trans, precond=precond))
                        res = solver.check(diag.trackers)

                        if res != z3.unsat:
                            logger.debug('found predecessor via %s' % trans.name)
                            m = Model(self.prog, solver.model(diag.trackers), KEY_NEW, KEY_OLD)
                            # if logger.isEnabledFor(logging.DEBUG):
                            #     logger.debug(str(m))
                            return (res, (phase_transition, (src_phase, m.as_diagram(old=True))))
                        elif args.use_z3_unsat_cores:
                            assert core is not None
                            uc = solver.unsat_core()
                            # if logger.isEnabledFor(logging.DEBUG):
                            #     logger.debug('uc')
                            #     logger.debug(str(sorted(uc, key=lambda y: y.decl().name())))

                                # logger.debug('assertions')
                                # logger.debug(str(solver.assertions()))

                            res = solver.check([diag.trackers[i] for i in core])
                            if res == z3.unsat:
                                logger.debug('but existing core sufficient, skipping')
                                continue

                            for x in sorted(uc, key=lambda y: y.decl().name()):
                                assert isinstance(x, z3.ExprRef)
                                core.add(int(x.decl().name()[1:]))
                            if logger.isEnabledFor(logging.DEBUG):
                                logger.debug('new core')
                                logger.debug(str(sorted(core)))

                return (z3.unsat, None)

    def clause_implied_by_transitions_from_frame(
            self,
            pre_frame: Frame,
            current_phase: Phase,
            c: Expr,
            solver: Optional[Solver]=None
    ) -> Optional[Tuple[Phase, Tuple[z3.ModelRef, PhaseTransition]]]:
        if solver is None:
            solver = self.solver
        t = solver.get_translator(KEY_NEW, KEY_OLD)

        for src, transitions in self.automaton.transitions_to_grouped_by_src(current_phase).items():
            logger.debug("check transition from %s by %s" % (src.name(), str(list(transitions))))

            ans = check_two_state_implication_along_transitions(solver, self.prog, # TODO: OK to use clean solver here?
                                                                pre_frame.summary_of(src), transitions,
                                                                c)
            if ans is not None:
                return (src, ans)

        return None


    def _simplify_summary(self, f: MySet[Expr]) -> None:
        l = []
        for c in reversed(f.l):
            f_minus_c = [x for x in f.l if x in f.s and x is not c]
            if c not in self.safety and \
               check_implication(self.solver, f_minus_c, [c]) is None:
                logger.debug('removed %s' % c)
                f.s.remove(c)
            else:
                l.append(c)
        l.reverse()
        f.l = l


    @log_start_end_xml()
    def simplify(self) -> None:
        for i, f in enumerate(self.fs):
            for p in self.automaton.phases():
                with LogTag('simplify', frame=str(i)):
                    logger.debug('simplifying frame %d, pred %s' % (i, p.name()))
                    self._simplify_summary(f.summary_of(p))


    def print_frame(self, i: int, lvl: int=logging.INFO) -> None:
        f = self.fs[i]
        with LogTag('frame', i=str(i)):
            for p in self.automaton.phases():
                logger.log_list(lvl, ['frame %d of %s is' % (i, p.name())] + [str(x) for x in f.summary_of(p)])

    def print_frames(self, lvl: int=logging.INFO) -> None:
        for i, _ in enumerate(self.fs):
            self.print_frame(i, lvl=lvl)

    def search(self) -> Frame:
        while True:
            n = len(self) - 1
            with LogTag('frame', lvl=logging.INFO, n=str(n)):
                with LogTag('current-frames', lvl=logging.INFO):
                    self.print_frames()

                logger.info('considering frame %s' % (len(self) - 1,))

                f = self.get_inductive_frame()
                if f is not None:
                    logger.always_print('frame is safe and inductive. done!')
                    for p in self.automaton.phases():
                        logger.log_list(ALWAYS_PRINT, ['summary of %s: ' % p.name()] + [str(x) for x in f.summary_of(p)])
                    return f

                logger.info('frame is safe but not inductive. starting new frame')
                self.new_frame()

def get_safety(prog: Program) -> List[Expr]:
    if args.safety is not None:
        the_inv: Optional[InvariantDecl] = None
        for inv in prog.invs():
            if inv.name == args.safety:
                the_inv = inv
        if the_inv is None:
            raise Exception('No safety invariant named %s' % args.safety)
        safety: List[Expr] = [the_inv.expr]
    else:
        safety = [inv.expr for inv in prog.invs()]

    return safety


@log_start_end_xml(logging.INFO)
@log_start_end_time(logging.INFO)
def updr(s: Solver, prog: Program) -> None:
    if args.use_z3_unsat_cores:
        z3.set_param('smt.core.minimize', True)

    check_init(s, prog)

    if args.automaton:
        automaton = prog.the_automaton()
        if automaton is None:
            syntax.error(None,'--automaton requires the file to declare an automaton')
    else:
        automaton = None

    fs = Frames(s, prog, automaton=automaton)
    fs.search()

def debug_tokens(filename: str) -> None:
    l = parser.get_lexer()

    with open(filename) as f:
        l.input(f.read())

    while True:
        tok = l.token()
        if not tok:
            break      # No more input
        logger.always_print(str(tok))


def check_automaton_init(s: Solver, prog: Program, a: AutomatonDecl) -> None:
    logger.always_print('checking automaton init:')

    t = s.get_translator(KEY_ONE)

    init_phase = prog.scope.get_phase(a.the_init().phase)
    assert init_phase is not None

    with s:
        for init in prog.inits():
            s.add(t.translate_expr(init.expr))

        for inv in init_phase.invs():
            with s:
                s.add(z3.Not(t.translate_expr(inv.expr)))

                if inv.tok is not None:
                    msg = ' on line %d' % inv.tok.lineno
                else:
                    msg = ''
                logger.always_print('  implies phase invariant%s...' % msg)
                sys.stdout.flush()

                check_unsat([inv.tok], ['phase invariant%s may not hold in initial state' % msg], s, prog, KEY_ONE)

def check_automaton_edge_covering(s: Solver, prog: Program, a: AutomatonDecl) -> None:
    logger.always_print('checking automaton edge covering:')

    t = s.get_translator(KEY_NEW, KEY_OLD)

    for phase in a.phases():
        logger.always_print('  checking phase %s:' % phase.name)
        with s:
            for inv in phase.invs():
                s.add(t.translate_expr(inv.expr, old=True))

            for trans in prog.transitions():
                if any(delta.transition == trans.name and delta.precond is None for delta in phase.transitions()):
                    logger.always_print('    transition %s is covered trivially' % trans.name)
                    continue

                logger.always_print('    checking transition %s is covered' % trans.name)

                with s:
                    s.add(t.translate_transition(trans))
                    s.add(z3.And(*(z3.Not(t.translate_precond_of_transition(delta.precond, trans))
                                   for delta in phase.transitions() if trans.name == delta.transition)))

                    check_unsat([phase.tok, trans.tok],
                                ['transition %s is not covered by this phase' %
                                 (trans.name, ),
                                 'this transition misses transitions from phase %s' % (phase.name,)],
                                s, prog, KEY_NEW, KEY_OLD)


def check_automaton_safety(s: Solver, prog: Program, a: AutomatonDecl) -> None:
    logger.always_print('checking automaton safety:')

    t = s.get_translator(KEY_ONE)

    safety = []
    for d in a.safeties():
        inv = prog.scope.get_invariant(d.name)
        assert inv is not None
        safety.append(inv.expr)

    for phase in a.phases():
        logger.always_print('  checking phase %s:' % phase.name)
        res = check_implication(s, (inv.expr for inv in phase.invs()), safety)
        if res is not None:
            m = Model(prog, res, KEY_ONE)
            logger.always_print(str(m))
            syntax.print_error(phase.tok, 'phase characterization does not guarantee safety')


def check_automaton_inductiveness(s: Solver, prog: Program, a: AutomatonDecl) -> None:
    logger.always_print('checking automaton inductiveness:')

    t = s.get_translator(KEY_NEW, KEY_OLD)

    for phase in a.phases():
        logger.always_print('  checking phase %s:' % phase.name)

        with s:
            for inv in phase.invs():
                s.add(t.translate_expr(inv.expr, old=True))

            for delta in phase.transitions():
                trans = prog.scope.get_transition(delta.transition)
                assert trans is not None
                precond = delta.precond
                target = prog.scope.get_phase(delta.target) if delta.target is not None else phase
                assert target is not None

                trans_pretty = '(%s, %s)' % (trans.name, str(precond) if (precond is not None) else 'true')
                logger.always_print('    checking transition: %s' % trans_pretty)

                with s:
                    s.add(t.translate_transition(trans, precond=precond))
                    for inv in target.invs():
                        with s:
                            s.add(z3.Not(t.translate_expr(inv.expr)))

                            if inv.tok is not None:
                                msg = ' on line %d' % inv.tok.lineno
                            else:
                                msg = ''
                            logger.always_print('      preserves invariant%s...' % msg)
                            sys.stdout.flush()

                            check_unsat([inv.tok, trans.tok],
                                        ['invariant%s may not be preserved by transition %s in phase %s' %
                                         (msg, trans_pretty, phase.name),
                                         'this transition may not preserve invariant%s' % (msg,)],
                                        s, prog, KEY_NEW, KEY_OLD)

@log_start_end_time(logging.INFO)
def verify(s: Solver, prog: Program) -> None:
    a = prog.the_automaton()
    if a is None:
        if args.automaton == 'only':
            syntax.error(None, "--automaton='only' requires the file to declare an automaton")
    elif args.automaton != 'no':
        check_automaton_full(s, prog, a)

    if args.automaton != 'only':
        check_init(s, prog)
        check_transitions(s, prog)

    if not syntax.errored:
        logger.always_print('all ok!')
    else:
        logger.always_print('program has errors.')

def check_automaton_full(s: Solver, prog: Program, a: AutomatonDecl) -> None:
    check_automaton_init(s, prog, a)
    check_automaton_safety(s, prog, a)
    check_automaton_inductiveness(s, prog, a)
    check_automaton_edge_covering(s, prog, a)


def check_bmc(s: Solver, prog: Program, safety: Expr, depth: int) -> Optional[z3.ModelRef]:
    keys = ['state%d' % i for i in range(depth+1)]

    if logger.isEnabledFor(logging.DEBUG):
        logger.debug('check_bmc property: %s' % safety)
        logger.debug('check_bmc depth: %s' % depth)

    with s:
        t = s.get_translator(keys[0])
        for init in prog.inits():
            s.add(t.translate_expr(init.expr))

        t = s.get_translator(keys[-1])
        s.add(t.translate_expr(syntax.Not(safety)))

        for i in range(depth):
            t = s.get_translator(keys[i+1], keys[i])
            l = []
            for transition in prog.transitions():
                p = z3.Bool('p_%s_%s' % (i, transition.name))
                l.append(p)
                s.add(p == t.translate_transition(transition))
            p = z3.Bool('p_%s_%s' % (i, 'stutter'))
            l.append(p)
            s.add(p == z3.And(*t.frame([])))
            s.add(z3.Or(*l))

        # if logger.isEnabledFor(logging.DEBUG):
        #     logger.debug('assertions')
        #     logger.debug(str(s.assertions()))

        if s.check() != z3.unsat:
            return s.model()
        return None

@log_start_end_time()
def bmc(s: Solver, prog: Program) -> None:
    safety = syntax.And(*get_safety(prog))

    n = args.depth

    logger.always_print('bmc checking the following property to depth %d' % n)
    logger.always_print('  ' + str(safety))

    start = datetime.now()

    res = check_bmc(s, prog, safety, n)

    if res is None:
        logger.always_print('ok. (%s)' % (datetime.now() - start))
        sys.stdout.flush()
    else:
        logger.always_print('no! (%s)' % (datetime.now() - start))
        sys.stdout.flush()
        verbose_print_z3_model(res)

@log_start_end_time()
def theorem(s: Solver, prog: Program) -> None:
    logger.always_print('checking theorems:')

    for th in prog.theorems():
        if th.twostate:
            keys = [KEY_NEW, KEY_OLD]
        else:
            keys = [KEY_ONE]

        t = s.get_translator(*keys)

        if th.name is not None:
            msg = ' ' + th.name
        elif th.tok is not None:
            msg = ' on line %d' % th.tok.lineno
        else:
            msg = ''

        logger.always_print(' theorem%s...' % msg)
        sys.stdout.flush()

        with s:
            s.add(z3.Not(t.translate_expr(th.expr)))

            check_unsat([th.tok], ['theorem%s may not hold' % msg], s, prog, *keys)

def generate_parser(s: Solver, prog: Program) -> None:
    pass  # parser is generated implicitly by main when it parses the program

def parse_args() -> argparse.Namespace:
    argparser = argparse.ArgumentParser()

    subparsers = argparser.add_subparsers()
    all_subparsers = []

    verify_subparser = subparsers.add_parser('verify')
    verify_subparser.set_defaults(main=verify)
    all_subparsers.append(verify_subparser)

    updr_subparser = subparsers.add_parser('updr')
    updr_subparser.set_defaults(main=updr)
    all_subparsers.append(updr_subparser)

    bmc_subparser = subparsers.add_parser('bmc')
    bmc_subparser.set_defaults(main=bmc)
    all_subparsers.append(bmc_subparser)

    theorem_subparser = subparsers.add_parser('theorem')
    theorem_subparser.set_defaults(main=theorem)
    all_subparsers.append(theorem_subparser)

    generate_parser_subparser = subparsers.add_parser('generate-parser')
    generate_parser_subparser.set_defaults(main=generate_parser)
    all_subparsers.append(generate_parser_subparser)

    for s in all_subparsers:
        s.add_argument('--forbid-parser-rebuild', action='store_true',
                       help='force loading parser from disk (helps when running mypyvy from multiple processes)')
        s.add_argument('--log', default='warning', choices=['error', 'warning', 'info', 'debug'],
                       help='logging level')
        s.add_argument('--log-time', action='store_true',
                       help='make each log message include current time')
        s.add_argument('--log-xml', action='store_true',
                       help='log in XML format')
        s.add_argument('--seed', type=int, default=0, help="value for z3's smt.random_seed")
        s.add_argument('--print-program-repr', action='store_true',
                       help='print a machine-readable representation of the program after parsing')
        s.add_argument('--print-program', action='store_true',
                       help='print the program after parsing')
        s.add_argument('--key-prefix',
                       help='additional string to use in front of names sent to z3')
        s.add_argument('--minimize-models', action='store_true',
                       help='find models with minimal cardinality')

    updr_subparser.add_argument('--safety', help='name of invariant to use as safety property')
    updr_subparser.add_argument('--use-z3-unsat-cores', action='store_true',
                                help='generalize diagrams using unsat cores instead of brute force')
    updr_subparser.add_argument('--smoke-test', action='store_true',
                                help='(for debugging mypyvy itself) run bmc to confirm every conjunct added to a frame')
    updr_subparser.add_argument('--assert-inductive-trace', action='store_true',
                                help='(for debugging mypyvy itself) check that frames are always inductive')

    updr_subparser.add_argument('--simple-conjuncts', action='store_true',
                                help='substitute existentially quantified variables that are equal to constants')
    updr_subparser.add_argument('--simplify-diagram', action='store_true',
                                help='in diagram generation, substitute existentially quantified variables that are equal to constants')
    updr_subparser.add_argument('--automaton', action='store_true',
                                help='whether to run vanilla UPDR or phase UPDR')
    updr_subparser.add_argument('--dont-block-may-cexs', action='store_false',
                                help="don't treat failures to push as additional proof obligations")

    verify_subparser.add_argument('--automaton', default='yes', choices=['yes', 'no', 'only'],
                                  help="whether to use phase automata during verification. by default ('yes'), both non-automaton "
                                  "and autotomaton proofs are checked. 'no' means ignore automaton proofs. "
                                  "'only' means ignore non-automaton proofs.")

    bmc_subparser.add_argument('--safety', help='property to check')
    bmc_subparser.add_argument('--depth', type=int, default=3, metavar='N',
                               help='number of steps to check')

    argparser.add_argument('filename')

    return argparser.parse_args()

start: datetime

class MyFormatter(logging.Formatter):
    def __init__(self, fmt: str) -> None:
        super().__init__(fmt='%(levelname)s ' + fmt)
        self.withoutlevel = logging.Formatter(fmt='%(message)s')
        global start
        start = datetime.now()

    def format(self, record: Any) -> str:
        if record.levelno == ALWAYS_PRINT:
            return self.withoutlevel.format(record)
        else:
            return super().format(record)

    def formatTime(self, record: Any, datefmt: Optional[str]=None) -> str:
        return str((datetime.now() - start).total_seconds())

def main() -> None:
    global args
    args = parse_args()

    if args.log_xml:
        fmt = '%(message)s'
    elif args.log_time:
        fmt = '%(asctime)s %(filename)s:%(lineno)d: %(message)s'
    else:
        fmt = '%(filename)s:%(lineno)d: %(message)s'

    logger.setLevel(getattr(logging, args.log.upper(), None))
    handler = logging.StreamHandler(stream=sys.stdout)
    handler.setFormatter(MyFormatter(fmt))
    logging.root.addHandler(handler)
    # logger.addHandler(handler)

    if args.key_prefix is not None:
        global KEY_ONE
        global KEY_NEW
        global KEY_OLD

        KEY_ONE = args.key_prefix + '_' + KEY_ONE
        KEY_NEW = args.key_prefix + '_' + KEY_NEW
        KEY_OLD = args.key_prefix + '_' + KEY_OLD

    with LogTag('main', lvl=logging.INFO):
        logger.always_print(' '.join(['python3'] + sys.argv))


        logger.info('setting seed to %d' % args.seed)
        z3.set_param('smt.random_seed', args.seed)

        with open(args.filename) as f:
            l = parser.get_lexer()
            p = parser.get_parser(forbid_rebuild=args.forbid_parser_rebuild)
            prog: syntax.Program = p.parse(input=f.read(), lexer=l, filename=args.filename)

        if args.print_program_repr:
            logger.always_print(repr(prog))
        if args.print_program:
            logger.always_print(str(prog))

        prog.resolve()

        scope = prog.scope
        assert scope is not None
        assert len(scope.stack) == 0

        s = Solver(cast(Scope[z3.ExprRef], scope))
        t = s.get_translator()
        for a in prog.axioms():
            s.add(t.translate_expr(a.expr))


        args.main(s, prog)

        logger.info('total number of queries: %s' % s.nqueries)

if __name__ == '__main__':
    main()
