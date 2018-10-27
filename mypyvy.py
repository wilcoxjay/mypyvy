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
import sys
from typing import List, Any, Optional, Callable, Set, Tuple, Union, Iterable, \
    Dict, TypeVar, Sequence, overload, Generic, Iterator, cast
import z3

import parser
import syntax
from syntax import Expr, Program, Scope, ConstantDecl, RelationDecl, SortDecl, \
    FunctionDecl, TransitionDecl, InvariantDecl

logger = logging.getLogger(__file__)

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

        print('')
        print(m)
        for tok, msg in zip(toks, errmsgs):
            syntax.print_error(tok, msg)
    print('ok. (%s)' % (datetime.now() - start))
    sys.stdout.flush()

def check_init(s: Solver, prog: Program) -> None:
    print('checking init:')

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
                print('  implies invariant%s...' % msg, end='')
                sys.stdout.flush()

                check_unsat([inv.tok], ['invariant%s may not hold in initial state' % msg], s, prog, KEY_ONE)


def check_transitions(s: Solver, prog: Program) -> None:
    t = s.get_translator(KEY_NEW, KEY_OLD)

    with s:
        for inv in prog.invs():
            s.add(t.translate_expr(inv.expr, old=True))

        for trans in prog.transitions():
            print('checking transation %s:' % (trans.name,))

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
                        print('  preserves invariant%s...' % msg, end='')
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

    def conjuncts(self) -> Iterable[Tuple[Union[SortDecl, RelationDecl, ConstantDecl, FunctionDecl], int, Expr]]:
        for t1 in self.ineq_conjuncts():
            yield t1
        for t2 in self.rel_conjuncts():
            yield t2
        for t3 in self.const_conjuncts():
            yield t3
        for t4 in self.func_conjuncts():
            yield t4


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
        e = syntax.And(*(c for _, _, c in self.conjuncts()))
        if len(self.binder.vs) == 0:
            return e
        else:
            return syntax.Exists(self.binder.vs, e)

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
                m = res
                print('')
                out = io.StringIO()
                f = z3.Formatter() # type: ignore
                f.max_args = 10000
                print(f.max_args)
                pp = z3.PP() # type: ignore
                pp.max_lines = 10000
                pp(out, f(m))
                print(out.getvalue())
                assert False
            logger.debug('ok.')

    def check_valid(self, s: Solver, prog: Program, f: Iterable[Expr]) \
    -> Union[None, Tuple[z3.ModelRef, TransitionDecl], z3.ModelRef]:
        ans = check_two_state_implication_all_transitions(s, prog, f, syntax.Not(self.to_ast()))
        if ans is not None:
            return ans
        return self.valid_in_init(s, prog)

    @log_start_end_time()
    def generalize(self, s: Solver, prog: Program, f: Iterable[Expr], depth: Optional[int]=None) -> None:
        if logger.isEnabledFor(logging.DEBUG):
            logger.debug('generalizing diagram')
            logger.debug(str(self))
            logger.debug('previous frame is\n%s' % '\n'.join(str(x) for x in f))

        T = Union[SortDecl, RelationDecl, ConstantDecl, FunctionDecl]
        d: T
        I: Iterable[T] = self.ineqs
        R: Iterable[T] = self.rels
        C: Iterable[T] = self.consts
        F: Iterable[T] = self.funcs

        if logger.isEnabledFor(logging.DEBUG):
            logger.debug('checking that transition relation itself is SAT from previous frame...')
            res1 = check_two_state_implication_all_transitions(s, prog, f, syntax.Bool(None, False))
            if res1 is None:
                assert False
            m, t = res1
            print(m)
            print(t.name)

        self.smoke(s, prog, depth)

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
            elif logger.isEnabledFor(logging.DEBUG):

                logger.debug('failed to eliminate clause %s' % c)
                logger.debug('from diagram %s' % self)

                if isinstance(res, tuple):
                    m, t = res
                    logger.debug('because of transition %s' % t.name)
                    logger.debug('and model %s' % Model(prog, m, KEY_NEW, KEY_OLD))
                else:
                    logger.debug('because the diagram is satisfiable in the initial state')
                    logger.debug('and model %s' % Model(prog, m, KEY_ONE))



        self.prune_unused_vars()

        if logger.isEnabledFor(logging.DEBUG):
            logger.debug('generalized diag')
            logger.debug(str(self))

class OrderedSet(Generic[T], Iterable[T]):
    def __init__(self, contents: Optional[Iterable[T]]=None) -> None:
        self.l: List[T] = []
        self.s: Set[T] = set()

        if contents is None:
            contents = []

        for x in contents:
            self.add(x)

    def __len__(self) -> int:
        return len(self.l)

    def __str__(self) -> str:
        return '{%s}' % ','.join(str(x) for x in self.l)

    def __contains__(self, item: T) -> bool:
        return item in self.s

    def add(self, x: T) -> None:
        if x not in self.s:
            self.l.append(x)
            self.s.add(x)

    def remove(self, x: T) -> None:
        if x not in self.s:
            raise

    def __isub__(self, other: Set[T]) -> OrderedSet[T]:
        self.s -= other
        self.l = [x for x in self.l if x in self.s]
        return self

    def __iter__(self) -> Iterator[T]:
        return iter(self.l)

MySet = OrderedSet

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

class Frames(object):
    def __init__(self, solver: Solver, prog: Program, safety: Sequence[Expr]) -> None:
        self.solver = solver
        self.prog = prog
        self.safety = safety
        self.fs: List[MySet[Expr]] = []
        self.push_cache: List[Set[Expr]] = []
        self.counter = 0
        self.uncommitted: Set[Expr] = set()

        self.new_frame(init.expr for init in prog.inits())

        # safety of initial state is checked before instantiating Frames
        for c in safety:
            self[-1].add(c)

        self.new_frame()



    def __getitem__(self, i: int) -> MySet[Expr]:
        return self.fs[i]

    def __setitem__(self, i: int, e: MySet[Expr]) -> None:
        assert e is self.fs[i]

    def __len__(self) -> int:
        return len(self.fs)

    def new_frame(self, contents: Optional[Iterable[Expr]]=None) -> None:
        if contents is None:
            contents = [syntax.Bool(None, True)]
        self.fs.append(MySet(contents))
        self.push_cache.append(set())

        self.push_forward_frames()
        self.simplify()

    def get_inductive_frame(self) -> Optional[MySet[Expr]]:
        for i in range(len(self) - 1):
            if check_implication(self.solver, self[i+1], self[i]) is None:
                return self[i+1]
        return None

    def push_forward_frames(self) -> None:
        for i, f in enumerate(self.fs[:-1]):
            logger.debug('pushing in frame %d' % i)

            frame_old_count = self.counter
            j = 0
            while j < len(f):
                assert self.uncommitted == set()
                c = f.l[j]
                if c in self[i+1] or c in self.push_cache[i]:
                    j += 1
                    continue

                is_safety = c in self.safety
                conjunct_old_count = self.counter

                while True:
                    logger.debug('frame %s attempting to push %s' % (i, c))

                    if not is_safety and args.convergence_hacks and (
                            self.counter > conjunct_old_count + 3 or
                            self.counter > frame_old_count + 10
                        ): # total hack
                        logger.warning('decided to give up pushing conjunct %s in frame %d' % (c, i))
                        if self.counter > conjunct_old_count + 3:
                            logger.warning("because I've tried to push this conjunct 3 times")
                        else:
                            assert self.counter > frame_old_count + 10
                            logger.warning("because I've spent too long in this frame")
                        self.abort()
                        break


                    res = check_two_state_implication_all_transitions(self.solver, self.prog, f, c)
                    if res is None:
                        logger.debug('frame %s managed to push %s' % (i, c))

                        if args.smoke_test:
                            logger.debug('jrw smoke testing...')
                            om = check_bmc(self.solver, self.prog, c, i+1)
                            if om is not None:
                                logger.debug('no!')
                                m = om
                                print('')
                                out = io.StringIO()
                                fmt = z3.Formatter() # type: ignore
                                fmt.max_args = 10000
                                print(fmt.max_args)
                                pp = z3.PP() # type: ignore
                                pp.max_lines = 10000
                                pp(out, fmt(m))
                                print(out.getvalue())
                                assert False
                            logger.debug('ok.')

                        self[i+1].add(c)
                        self.commit()
                        break
                    else:
                        m, t = res
                        mod = Model(self.prog, m, KEY_NEW, KEY_OLD)
                        diag = mod.as_diagram(old=True)
                        if logger.isEnabledFor(logging.DEBUG):
                            logger.debug('frame %s failed to immediately push %s due to transition %s' % (i, c, t.name))
                            # logger.debug(str(mod))
                        flag = False
                        if flag:
                            flag = False
                            self.abort()
                            break
                        if is_safety:
                            logger.debug('note: current clause is safety condition')
                            self.block(diag, i, [(None, c), (t, diag)], True)
                        else:
                            ans = self.block(diag, i, [(None, c), (t, diag)], False)
                            if isinstance(ans, GaveUp):
                                logger.warning('frame %d decided to give up pushing conjunct %s' % (i, c))
                                logger.warning('because a call to block gave up')
                                self.abort()
                                break
                            elif isinstance(ans, CexFound):
                                self.commit()
                                break

                self.push_cache[i].add(c)
                j += 1

    def block(
            self,
            diag: Diagram,
            j: int,
            trace: List[Tuple[Optional[TransitionDecl],Union[Diagram, Expr]]]=[],
            safety_goal: bool=True
    ) -> Union[Blocked, CexFound, GaveUp]:
        if j == 0 or (j == 1 and diag.valid_in_init(self.solver, self.prog) is not None):
            if safety_goal:
                print('\n'.join(((t.name + ' ') if t is not None else '') + str(diag) for t, diag in trace))
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
                logger.debug(str(diag))

                logger.debug('frame %d is' % (j-1))
                logger.debug('\n'.join(str(x) for x in self[j-1]))
            res, x = self.find_predecessor(self[j-1], diag)
            if res == z3.unsat:
                logger.debug('no predecessor: blocked!')
                assert x is None or isinstance(x, MySet)
                core: Optional[MySet[int]] = x
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
            logger.debug(str(e))

        self.add(e, j)

        return Blocked()


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

        if args.smoke_test:
            logger.debug('smoke testing at depth %s...' % (depth,))
            res = check_bmc(self.solver, self.prog, e, depth)
            if res is not None:
                logger.debug('no!')
                m = res
                print('')
                out = io.StringIO()
                f = z3.Formatter() # type: ignore
                f.max_args = 10000
                print(f.max_args)
                pp = z3.PP() # type: ignore
                pp.max_lines = 10000
                pp(out, f(m))
                print(out.getvalue())
                assert False
            logger.debug('ok.')

        for i in range(depth+1):
            self[i].add(e)


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


    def simplify(self) -> None:
        for i, f in enumerate(self.fs):
            logger.debug('simplifying frame %d' % i)
            self._simplify_frame(f)


    def print_frames(self) -> None:
        for i, f in enumerate(self.fs):
            logger.info('frame %d is\n%s' % (i, '\n'.join(str(x) for x in f)))
            logger.info('')

    def search(self) -> MySet[Expr]:
        while True:
            f: Optional[OrderedSet[Expr]]
            self.print_frames()
            logger.info('considering frame %s' % (len(self) - 1,))

            f = self.get_inductive_frame()
            if f is not None:
                print('frame is safe and inductive. done!')
                print('\n'.join(str(x) for x in f))
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


@log_start_end_time(logging.INFO)
def updr(s: Solver, prog: Program) -> None:
    if args.find_predecessor_via_transition_disjunction:
        args.use_z3_unsat_cores = True

    if args.use_z3_unsat_cores:
        z3.set_param('smt.core.minimize', True)

    check_init(s, prog)

    fs = Frames(s, prog, get_safety(prog))
    fs.search()

def debug_tokens(filename: str) -> None:
    l = parser.get_lexer()

    with open(filename) as f:
        l.input(f.read())

    while True:
        tok = l.token()
        if not tok: 
            break      # No more input
        print(tok)

@log_start_end_time(logging.INFO)
def verify(s: Solver, prog: Program) -> None:
    check_init(s, prog)
    check_transitions(s, prog)

    print('all ok!')

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

    print('bmc checking the following property to depth %d' % n)
    print('  ' + str(safety))

    start = datetime.now()

    res = check_bmc(s, prog, safety, n)

    if res is None:
        print('ok. (%s)' % (datetime.now() - start))
        sys.stdout.flush()
    else:
        m = res
        print('')
        out = io.StringIO()
        f = z3.Formatter() # type: ignore
        f.max_args = 10000
        print(f.max_args)
        pp = z3.PP() # type: ignore
        pp.max_lines = 10000
        pp(out, f(m))
        print(out.getvalue())
        # print(m)
        print('no! (%s)' % (datetime.now() - start))
        sys.stdout.flush()



@log_start_end_time()
def theorem(s: Solver, prog: Program) -> None:
    print('checking theorems:')

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

        print(' theorem%s...' % msg)
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

    bmc_subparser.add_argument('--safety', help='property to check')
    bmc_subparser.add_argument('--depth', type=int, default=3, metavar='N',
                               help='number of steps to check')

    argparser.add_argument('filename')

    return argparser.parse_args()

class MyFormatter(logging.Formatter):
    def __init__(self, fmt: str) -> None:
        super().__init__(fmt=fmt)
        self.start = datetime.now()

    def formatTime(self, record: Any, datefmt: Optional[str]=None) -> str:
        return str((datetime.now() - self.start).total_seconds())

def main() -> None:
    print(' '.join(['python3'] + sys.argv))

    global args
    args = parse_args()

    if args.log_time:
        fmt = '%(levelname)s %(asctime)s %(filename)s:%(lineno)d: %(message)s'
    else:
        fmt = '%(levelname)s %(filename)s:%(lineno)d: %(message)s'

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

    logger.info('setting seed to %d' % args.seed)
    z3.set_param('smt.random_seed', args.seed)

    with open(args.filename) as f:
        l = parser.get_lexer()
        p = parser.get_parser(forbid_rebuild=args.forbid_parser_rebuild)
        prog: syntax.Program = p.parse(input=f.read(), lexer=l, filename=args.filename)

    if args.print_program_repr:
        print(repr(prog))
    if args.print_program:
        print(prog)

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
