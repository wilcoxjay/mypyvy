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

from phases import PhaseAutomaton, Phase

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

    def get_translator(self, key: Optional[str]=None, key_old: Optional[str]=None) \
        -> syntax.Z3Translator:
        t = (key, key_old)
        if t not in self.translators:
            self.translators[t] = syntax.Z3Translator(self.scope, key, key_old)
        return self.translators[t]

    def __enter__(self) -> None:
        self.z3solver.push()

    def __exit__(self, exn_type: Any, exn_value: Any, traceback: Any) -> None:
        self.z3solver.pop()

    def add(self, e: z3.ExprRef) -> None:
        # if logger.isEnabledFor(logging.DEBUG):
        #     logger.debug('adding %s' % e)

        self.z3solver.add(e)

    def check(self, *assumptions: z3.ExprRef) -> z3.CheckSatResult:
        # logger.debug('solver.check')
        self.nqueries += 1
        return self.z3solver.check(*assumptions)

    def model(self, *assumptions: z3.ExprRef) -> z3.ModelRef:
        if args.minimize_models:
            return self._minimal_model(*assumptions)
        else:
            return self.z3solver.model()

    def _cardinality_constraint(self, s: z3.SortRef, n: int) -> z3.ExprRef:
        x = z3.Const('x', s)
        disjs = []
        for i in range(n):
            c = z3.Const('card_%s_%s' % (s.name(), i), s)
            disjs.append(x == c)

        return z3.Forall(x, z3.Or(*disjs))

    def _minimal_model(self, *assumptions: z3.ExprRef) -> z3.ModelRef:
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
                        res = self.check(*assumptions)
                        if res == z3.sat:
                            break
                    n += 1
                if n < len(u):
                    self.add(self._cardinality_constraint(s, n))
            assert self.check(*assumptions) == z3.sat
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

    def __str__(self) -> str:
        return 'exists %s.\n  %s' % (
            ', '.join(v.name for v in self.binder.vs),
            ' &\n  '.join(str(c) for _, _, c in self.conjuncts())
        )

    def resolve(self, scope: Scope) -> None:
        self.binder.pre_resolve(scope)

        with scope.in_scope([(v, v.sort) for v in self.binder.vs]):
            for _, _, c in self.conjuncts():
                c.resolve(scope, syntax.BoolSort)

        self.binder.post_resolve()

    def to_z3(self, t: syntax.Z3Translator) -> z3.ExprRef:
        bs = t.bind(self.binder)
        with t.scope.in_scope(list(zip(self.binder.vs, bs))):
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

    def valid_in_init(self, s: Solver, prog: Program) -> Optional[z3.ModelRef]:
        return check_implication(s, (init.expr for init in prog.inits()), [syntax.Not(self.to_ast())])

    def minimize_from_core(self, core: Optional[Iterable[int]]) -> None:
        if core is None:
            return

        I: Dict[SortDecl, List[Expr]] = {}
        R: Dict[RelationDecl, List[Expr]] = {}
        C: Dict[ConstantDecl, Expr] = {}
        F: Dict[FunctionDecl, List[Expr]] = {}

        started = False

        for i in core:
            started = True
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

        assert started

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

    def check_valid(self, s: Solver, prog: Program, f: Iterable[Expr]) \
    -> Union[None, Tuple[z3.ModelRef, TransitionDecl], z3.ModelRef]:
        ans = check_two_state_implication_all_transitions(s, prog, f, syntax.Not(self.to_ast()))
        if ans is not None:
            return ans
        return self.valid_in_init(s, prog)

    @log_start_end_xml()
    @log_start_end_time()
    def generalize(self, s: Solver, prog: Program, f: Iterable[Expr], depth: Optional[int]=None) -> None:
        if logger.isEnabledFor(logging.DEBUG):
            logger.debug('generalizing diagram')
            logger.debug(str(self))
            with LogTag('previous-frame', lvl=logging.DEBUG):
                logger.log_list(logging.DEBUG, ['previous frame is'] + [str(x) for x in f])

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
                    res = self.check_valid(s, prog, f)
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
                        res = self.check_valid(s, prog, f)
                    if res is None:
                        if logger.isEnabledFor(logging.DEBUG):
                            logger.debug('eliminated all negative conjuncts from declaration %s' % d)
                        self.remove_clause(d, cs)
                        self.smoke(s, prog, depth)

            for d, j, c in self.conjuncts():
                with self.without(d, j):
                    res = self.check_valid(s, prog, f)
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
    def __init__(self, solver: Solver, prog: Program, safety: Sequence[Expr], automaton: Optional[AutomatonDecl]=None) -> None:
        self.solver = solver
        self.prog = prog
        self.safety = safety
        assert automaton is not None
        self.automaton = PhaseAutomaton(automaton)
        self.fs: List[MySet[Expr]] = []
        self.push_cache: List[Set[Expr]] = []
        self.counter = 0
        self.uncommitted: Set[Expr] = set()
        self.learned_order: 'networkx.DiGraph[Expr]' = networkx.DiGraph()

        init_conjuncts = [init.expr for init in prog.inits()]
        self.new_frame({p: init_conjuncts if p == self.automaton.init_phase()
                            else syntax.FalseExpr
                        for p in self.automaton.phases()})

        self.new_frame()

    def __getitem__(self, i: int) -> MySet[Expr]:
        return self.fs[i]

    def __setitem__(self, i: int, e: MySet[Expr]) -> None:
        assert e is self.fs[i]

    def __len__(self) -> int:
        return len(self.fs)

    def new_frame(self, contents: Optional[Dict[Phase, Sequence[Expr]]]=None) -> None:
        if contents is None:
            contents = [syntax.Bool(None, True)]
        self.fs.append(MySet(contents))
        self.push_cache.append(set())
        for c in contents:
            self.learned_order.add_node(c)

        self.push_forward_frames()
        self.establish_safety()
        self.simplify()


    @log_start_end_xml()
    def establish_safety(self) -> None:
        frame_no = len(self.fs) - 1
        f = self.fs[-1]

        while True:
            with LogTag('establish-safety-attempt'):
                res = check_implication(self.solver, f, self.safety)

                if res is None:
                    self.commit()
                    return

                z3m: z3.ModelRef = res

                mod = Model(self.prog, z3m, KEY_ONE)
                diag = mod.as_diagram()
                self.block(diag, frame_no, [(None, diag)], True)


    def get_inductive_frame(self) -> Optional[MySet[Expr]]:
        for i in range(len(self) - 1):
            if check_implication(self.solver, self[i+1], self[i]) is None:
                return self[i+1]
        return None

    def  push_conjunct(self, frame_no: int, c: Expr, frame_old_count: Optional[int]=None) -> None:
        is_safety = c in self.safety
        conjunct_old_count = self.counter

        f = self.fs[frame_no]
        while True:
            with LogTag('pushing-conjunct-attempt', lvl=logging.DEBUG, frame=str(frame_no), conj=str(c)):
                logger.debug('frame %s attempting to push %s' % (frame_no, c))

                if not is_safety and args.convergence_hacks and (
                        self.counter > conjunct_old_count + 3 or
                        (frame_old_count is not None and self.counter > frame_old_count + 10)
                    ): # total hack
                    logger.warning('decided to give up pushing conjunct %s in frame %d' % (c, frame_no))
                    if self.counter > conjunct_old_count + 3:
                        logger.warning("because I've tried to push this conjunct 3 times")
                    else:
                        assert frame_old_count is not None and self.counter > frame_old_count + 10
                        logger.warning("because I've spent too long in this frame")
                    self.abort()
                    break

                res = check_two_state_implication_all_transitions(self.solver, self.prog, f, c)
                if res is None:
                    logger.debug('frame %s managed to push %s' % (frame_no, c))

                    if args.smoke_test and logger.isEnabledFor(logging.DEBUG):
                        logger.debug('jrw smoke testing...')
                        om = check_bmc(self.solver, self.prog, c, frame_no+1)
                        if om is not None:
                            logger.debug('no!')
                            verbose_print_z3_model(om)
                        logger.debug('ok.')

                    self[frame_no+1].add(c)
                    self.commit()
                    break
                else:
                    m, t = res
                    mod = Model(self.prog, m, KEY_NEW, KEY_OLD)
                    diag = mod.as_diagram(old=True)
                    if logger.isEnabledFor(logging.DEBUG):
                        logger.debug('frame %s failed to immediately push %s due to transition %s' % (frame_no, c, t.name))
                        # logger.debug(str(mod))
                    if is_safety:
                        logger.debug('note: current clause is safety condition')
                        self.block(diag, frame_no, [(None, c), (t, diag)], True)
                    else:
                        ans = self.block(diag, frame_no, [(None, c), (t, diag)], False)
                        if isinstance(ans, GaveUp):
                            logger.warning('frame %d decided to give up pushing conjunct %s' % (frame_no, c))
                            logger.warning('because a call to block gave up')
                            self.abort()
                            break
                        elif isinstance(ans, CexFound):
                            self.commit()
                            break

    @log_start_end_xml(logging.DEBUG)
    def push_forward_frames(self) -> None:
        for i, f in enumerate(self.fs[:-1]):
            with LogTag('pushing-frame', lvl=logging.DEBUG, i=str(i)):
                logger.debug('pushing in frame %d' % i)

                frame_old_count = self.counter

                def process_conjunct(c: Expr) -> None:
                    if c in self[i+1] or c in self.push_cache[i]:
                        return

                    with LogTag('pushing-conjunct', lvl=logging.DEBUG, frame=str(i), conj=str(c)):
                        self.push_conjunct(i, c, frame_old_count)

                    self.push_cache[i].add(c)

                j = 0
                if args.push_toposort:
                    j = len(f)
                    G = networkx.graphviews.subgraph_view(self.learned_order, lambda x: x in f)

                    if logger.isEnabledFor(logging.DEBUG):
                        for c in f:
                            if c not in G:
                                print('c =', c)
                                print('G =', ', '.join(str(x) for x in G))
                                self.print_frames()
                                assert False

                    for c in networkx.topological_sort(G):
                        assert self.uncommitted == set()
                        process_conjunct(c)

                while j < len(f):
                    assert self.uncommitted == set()
                    c = f.l[j]
                    process_conjunct(c)
                    j += 1

    # Block the diagram in the given frame.
    # If safety_goal is True, the only possible outcomes are returning Blocked() on success
    # or throwing an exception describing an abstract counterexample on failure.
    # If safety_goal is False, then no abstract counterexample is ever reported to user,
    # instead, CexFound() is returned to indicate the diagram could not be blocked.
    # Also, if safety_goal is False and args.convergence_hacks is True, block() will
    # sometimes decide to give up blocking and return GaveUp(), which the caller
    # can handle in whatever way makes sense (typically, it is treated as a failure to block).
    @log_start_end_xml(lvl=logging.DEBUG)
    def block(
            self,
            diag: Diagram,
            j: int,
            trace: List[Tuple[Optional[TransitionDecl],Union[Diagram, Expr]]]=[],
            safety_goal: bool=True
    ) -> Union[Blocked, CexFound, GaveUp]:
        if j == 0 or (j == 1 and diag.valid_in_init(self.solver, self.prog) is not None):
            if safety_goal:
                logger.always_print('\n'.join(((t.name + ' ') if t is not None else '') + str(diag) for t, diag in trace))
                raise Exception('abstract counterexample')
            else:
                if logger.isEnabledFor(logging.DEBUG):
                    logger.debug('failed to block diagram')
                    # logger.debug(str(diag))
                return CexFound()

        old_count = self.counter

        # print fs
        while True:
            if not safety_goal and args.convergence_hacks and self.counter >= old_count + 3:
                if logger.isEnabledFor(logging.DEBUG):
                    logger.warning('decided to give up blocking diagram after 3 tries in frame %s' % j)
                    logger.debug(str(diag))
                return GaveUp()

            if logger.isEnabledFor(logging.DEBUG):
                logger.debug('blocking diagram in frame %s' % j)
                log_diagram(diag, lvl=logging.DEBUG)

                self.print_frame(j-1, lvl=logging.DEBUG)
            res, x = self.find_predecessor(self[j-1], diag)
            if res == z3.unsat:
                logger.debug('no predecessor: blocked!')
                assert x is None or isinstance(x, MySet)
                core: Optional[MySet[int]] = x
                self.augment_core_for_init(diag, core)
                break
            assert isinstance(x, tuple), (res, x)
            trans, pre_diag = x

            trace.append(x)
            ans = self.block(pre_diag, j-1, trace, safety_goal)
            if not isinstance(ans, Blocked):
                return ans
            trace.pop()

        if logger.isEnabledFor(logging.DEBUG) and core is not None:
            logger.debug('core %s' % core)
            logger.debug('unminimized diag\n%s' % diag)

        diag.minimize_from_core(core)
        diag.generalize(self.solver, self.prog, self[j-1], j)

        e = syntax.Not(diag.to_ast())

        if logger.isEnabledFor(logging.DEBUG):
            logger.debug('adding new clause to frames 0 through %d' % j)
        if logger.isEnabledFor(logging.INFO):
            logger.info("[%d] %s" % (j, str(e)))

        c = trace[0][1]
        if isinstance(c, Expr):
            self.learned_order.add_edge(e, c)

        self.add(e, j)

        return Blocked()


    def augment_core_for_init(self, diag: Diagram, core: Optional[MySet[int]]) -> None:
        if core is None or not args.use_z3_unsat_cores:
            return

        t = self.solver.get_translator(KEY_ONE)

        with self.solver:
            for init in self.prog.inits():
                self.solver.add(t.translate_expr(init.expr))

            self.solver.add(diag.to_z3(t))

            res = self.solver.check(*diag.trackers)

            assert res == z3.unsat
            uc = self.solver.unsat_core()
            # if logger.isEnabledFor(logging.DEBUG):
            #     logger.debug('uc')
            #     logger.debug(str(sorted(uc, key=lambda y: y.decl().name())))

                # logger.debug('assertions')
                # logger.debug(str(self.solver.assertions()))

            res = self.solver.check(*[diag.trackers[i] for i in core])
            if res == z3.unsat:
                logger.debug('augment_core_for_init: existing core sufficient')
                return

            for x in sorted(uc, key=lambda y: y.decl().name()):
                assert isinstance(x, z3.ExprRef)
                core.add(int(x.decl().name()[1:]))
            if logger.isEnabledFor(logging.DEBUG):
                logger.debug('augment_core_for_init: new core')
                logger.debug(str(sorted(core)))

    def commit(self) -> None:
        self.uncommitted = set()

    def abort(self) -> None:
        if logger.isEnabledFor(logging.DEBUG):
            logger.debug('aborting')
            logger.debug('\n'.join(str(x) for x in self.uncommitted))
        for i in range(len(self)):
            self[i] -= self.uncommitted
        self.uncommitted = set()

    def add(self, e: Expr, depth: Optional[int]=None) -> None:
        self.counter += 1
        self.uncommitted.add(e)

        if depth is None:
            depth = len(self)

        if args.smoke_test and logger.isEnabledFor(logging.DEBUG):
            logger.debug('smoke testing at depth %s...' % (depth,))
            res = check_bmc(self.solver, self.prog, e, depth)
            if res is not None:
                logger.debug('no!')
                verbose_print_z3_model(res)
            logger.debug('ok.')

        for i in range(depth+1):
            self[i].add(e)


    @log_start_end_xml(lvl=logging.DEBUG)
    def find_predecessor(
            self,
            pre_frame: Iterable[Expr],
            diag: Diagram
    ) -> Tuple[z3.CheckSatResult, Union[Optional[MySet[int]], Tuple[TransitionDecl, Diagram]]]:
        if args.use_z3_unsat_cores:
            core: MySet[int] = MySet()

        t = self.solver.get_translator(KEY_NEW, KEY_OLD)

        with self.solver:
            for f in pre_frame:
                self.solver.add(t.translate_expr(f, old=True))

            self.solver.add(diag.to_z3(t))

            for trans in self.prog.transitions():
                logger.debug('checking %s' % trans.name)
                with self.solver:
                    self.solver.add(t.translate_transition(trans))
                    # if logger.isEnabledFor(logging.DEBUG):
                    #     logger.debug('assertions')
                    #     logger.debug(str(self.solver.assertions()))
                    res = self.solver.check(*diag.trackers)

                    if res != z3.unsat:
                        logger.debug('found predecessor via %s' % trans.name)
                        m = Model(self.prog, self.solver.model(*diag.trackers), KEY_NEW, KEY_OLD)
                        # if logger.isEnabledFor(logging.DEBUG):
                        #     logger.debug(str(m))
                        return (res, (trans, m.as_diagram(old=True)))
                    elif args.use_z3_unsat_cores and not args.find_predecessor_via_transition_disjunction:
                        uc = self.solver.unsat_core()
                        # if logger.isEnabledFor(logging.DEBUG):
                        #     logger.debug('uc')
                        #     logger.debug(str(sorted(uc, key=lambda y: y.decl().name())))

                            # logger.debug('assertions')
                            # logger.debug(str(self.solver.assertions()))

                        res = self.solver.check(*[diag.trackers[i] for i in core])
                        if res == z3.unsat:
                            logger.debug('but existing core sufficient, skipping')
                            continue

                        for x in sorted(uc, key=lambda y: y.decl().name()):
                            assert isinstance(x, z3.ExprRef)
                            core.add(int(x.decl().name()[1:]))
                        if logger.isEnabledFor(logging.DEBUG):
                            logger.debug('new core')
                            logger.debug(str(sorted(core)))

            if args.find_predecessor_via_transition_disjunction:
                ts = []
                revmap = []
                for k, trans in enumerate(self.prog.transitions()):
                    tx = z3.Bool('t%d' % k)
                    ts.append(tx)
                    self.solver.add(tx == t.translate_transition(trans))
                    revmap.append(trans)
                self.solver.add(z3.Or(*ts))
                res = self.solver.check(*diag.trackers)
                assert res == z3.unsat
                # if res != z3.unsat:
                #     z3mod = self.solver.model()
                #     the_trans: Optional[TransitionDecl] = None
                #     for k, tx in enumerate(ts):
                #         if z3mod.eval(tx):
                #             the_trans = revmap[k]
                #             break
                #     else:
                #         assert False
                #
                #     logger.debug('found predecessor via %s' % the_trans.name)
                #     m = Model(self.prog, z3mod, KEY_NEW, KEY_OLD)
                #     return (res, (trans, m.as_diagram(old=True)))
                # else:
                if True:
                    assert args.use_z3_unsat_cores

                    uc = self.solver.unsat_core()
                    # if logger.isEnabledFor(logging.DEBUG):
                    #     logger.debug('uc')
                    #     logger.debug(str(sorted(uc, key=lambda y: y.decl().name())))

                        # logger.debug('assertions')
                        # logger.debug(str(self.solver.assertions()))

                    for x in sorted(uc, key=lambda y: y.decl().name()):
                        assert isinstance(x, z3.ExprRef)
                        core.add(int(x.decl().name()[1:]))
                    if logger.isEnabledFor(logging.DEBUG):
                        logger.debug('core')
                        logger.debug(str(sorted(core)))


        if not args.use_z3_unsat_cores:
            ret_core: Optional[MySet[int]] = None
        else:
            ret_core = MySet(sorted(core))

        return (z3.unsat, ret_core)

    def _simplify_frame(self, f: MySet[Expr]) -> None:
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
            with LogTag('simplify', frame=str(i)):
                logger.debug('simplifying frame %d' % i)
                self._simplify_frame(f)


    def print_frame(self, i: int, lvl: int=logging.INFO) -> None:
        f = self.fs[i]
        with LogTag('frame', i=str(i)):
            logger.log_list(lvl, ['frame %d is' % i] + [str(x) for x in f])

    def print_frames(self) -> None:
        for i, _ in enumerate(self.fs):
            self.print_frame(i)

    def search(self) -> MySet[Expr]:
        while True:
            f: Optional[OrderedSet[Expr]]
            n = len(self) - 1
            with LogTag('frame', lvl=logging.INFO, n=str(n)):
                with LogTag('current-frames', lvl=logging.INFO):
                    self.print_frames()

                logger.info('considering frame %s' % (len(self) - 1,))

                f = self.get_inductive_frame()
                if f is not None:
                    logger.always_print('frame is safe and inductive. done!')
                    logger.log_list(ALWAYS_PRINT, [str(x) for x in f])
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
    if args.find_predecessor_via_transition_disjunction:
        args.use_z3_unsat_cores = True

    if args.use_z3_unsat_cores:
        z3.set_param('smt.core.minimize', True)

    check_init(s, prog)

    fs = Frames(s, prog, get_safety(prog))
    fs.search()

@log_start_end_xml(logging.INFO)
@log_start_end_time(logging.INFO)
def phase_updr(s: Solver, prog: Program) -> None:
    # TODO: handle these
    if args.find_predecessor_via_transition_disjunction:
        args.use_z3_unsat_cores = True

    if args.use_z3_unsat_cores:
        z3.set_param('smt.core.minimize', True)

    check_init(s, prog)

    fs = Frames(s, prog, get_safety(prog), automaton=prog.the_automaton())
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
                    # TODO: this is the full EA -> EA check which is generally undecidable
                    s.add(z3.And(*(z3.Not(t.translate_transition(trans, delta.precond))
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
    check_automaton_full(s, prog)

    check_init(s, prog)
    check_transitions(s, prog)

    if not syntax.errored:
        logger.always_print('all ok!')
    else:
        logger.always_print('program has errors.')

@log_start_end_time(logging.INFO)
def verify_automaton(s: Solver, prog: Program) -> None:
    check_automaton_full(s, prog)

    if not syntax.errored:
        logger.always_print('all ok!')
    else:
        logger.always_print('program has errors.')


def check_automaton_full(s: Solver, prog: Program) -> None:
    a = prog.the_automaton()
    if a is not None:
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

    verify_subparser = subparsers.add_parser('verify-automaton')
    verify_subparser.set_defaults(main=verify_automaton)
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
    updr_subparser.add_argument('--find-predecessor-via-transition-disjunction', action='store_true',
                                help='when searching for diagram predecessors, use a big disjunction ' +
                                'of all transitions rather than enumerating them one by one')
    updr_subparser.add_argument('--smoke-test', action='store_true',
                                help='run bmc to confirm every conjunct added to a frame')
    updr_subparser.add_argument('--convergence-hacks', action='store_true',
                                help='when some steps seem to be taking too long, just give up')
    updr_subparser.add_argument('--simple-conjuncts', action='store_true',
                                help='substitute existentially quantified variables that are equal to constants')
    updr_subparser.add_argument('--push-toposort', action='store_true',
                                help='push lemmas in each frame in dependency orded '
                                '(if lemma X was learned while pushing Y, then X will be pushed before Y in future frames)')


    bmc_subparser.add_argument('--safety', help='property to check')
    bmc_subparser.add_argument('--depth', type=int, default=3, metavar='N',
                               help='number of steps to check')

    argparser.add_argument('filename')

    phase_updr_subparser = subparsers.add_parser('phase-updr', parents=[updr_subparser], add_help=False)
    phase_updr_subparser.set_defaults(main=phase_updr)
    all_subparsers.append(phase_updr_subparser)

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
