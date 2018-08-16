import argparse
from collections import OrderedDict, defaultdict
from contextlib import contextmanager
import copy
from datetime import datetime
import functools
import itertools
import logging
import sys
from typing import List, Any, Optional, Callable, Set, Tuple, Union, Iterable, \
    Dict, TypeVar, Sequence, overload, Generic, Iterator, cast
import z3

import parser
import syntax
from syntax import Expr, Program, Scope, ConstantDecl, RelationDecl, SortDecl, \
    TransitionDecl, InvariantDecl

logger = logging.getLogger(__file__)

z3.Forall = z3.ForAll

args: Optional[argparse.Namespace] = None

class Solver(object):
    def __init__(self, scope: Scope[z3.ExprRef]) -> None:
        self.z3solver = z3.Solver()
        self.scope = scope
        self.translators: Dict[Tuple[Optional[str], Optional[str]], syntax.Z3Translator] = {}

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
        return self.z3solver.check(*assumptions)

    def model(self) -> z3.ModelRef:
        return self.z3solver.model()

    def assertions(self) -> Sequence[z3.ExprRef]:
        l = self.z3solver.assertions()
        return sorted(l, key=lambda x: str(x))

    def unsat_core(self) -> Sequence[z3.ExprRef]:
        return self.z3solver.unsat_core()


T = TypeVar('T')

def check_unsat(
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
        raise Exception('no')
    print('ok. (%s)' % (datetime.now() - start))
    sys.stdout.flush()

def check_init(s: Solver, prog: Program) -> None:
    print('checking init:')

    t = s.get_translator('one')

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

                check_unsat(s, prog, 'one')


def check_transitions(s: Solver, prog: Program) -> None:
    t = s.get_translator('new', 'old')

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

                        check_unsat(s, prog, 'new', 'old')

def check_implication(
        s: Solver,
        hyps: Iterable[Expr],
        concs: Iterable[Expr]
) -> Optional[z3.ModelRef]:
    t = s.get_translator('one')
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
) -> Optional[z3.ModelRef]:
    t = s.get_translator('new', 'old')
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
                    return s.model()

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
            logger.log(lvl, '%s ended at %s (took %s)' % (func.__name__, end, repr(end - start)))
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
            consts: Dict[ConstantDecl, Expr]
    ) -> None:
        self.binder = syntax.Binder(vs)
        self.ineqs = ineqs
        self.rels = rels
        self.consts = consts
        self.trackers: List[z3.ExprRef] = []
        self.tombstones: Dict[Union[SortDecl, RelationDecl, ConstantDecl], Set[int]] = \
            defaultdict(lambda: set())

    def conjuncts(self) -> Iterable[Tuple[Union[SortDecl, RelationDecl, ConstantDecl], int, Expr]]:
        for s, l in self.ineqs.items():
            for i, e in enumerate(l):
                if i not in self.tombstones[s]:
                    yield s, i, e
        for r, l in self.rels.items():
            for i, e in enumerate(l):
                if i not in self.tombstones[r]:
                    yield r, i, e
        for c, e in self.consts.items():
            if 0 not in self.tombstones[c]:
                yield c, 0, e

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
            self.reverse_map: List[Tuple[Union[SortDecl, RelationDecl, ConstantDecl], int]] = []
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

    def minimize_from_core(self, core: Iterable[int]) -> None:
        I: Dict[SortDecl, List[Expr]] = {}
        R: Dict[RelationDecl, List[Expr]] = {}
        C: Dict[ConstantDecl, Expr] = {}

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
            else:
                assert isinstance(d, ConstantDecl)
                assert d not in C
                C[d] = self.consts[d]

        assert started

        self.prune_unused_vars()

    def remove_clause(self, d: Union[SortDecl, RelationDecl, ConstantDecl], i: int) -> None:
        assert i not in self.tombstones[d]
        self.tombstones[d].add(i)

    def prune_unused_vars(self) -> None:
        self.binder.vs = [v for v in self.binder.vs
                          if any(v.name in c.free_ids() for _, _, c in self.conjuncts())]


    @contextmanager
    def without(self, d: Union[SortDecl, RelationDecl, ConstantDecl], j: int) -> Iterator[None]:
        assert j not in self.tombstones[d]
        self.tombstones[d].add(j)
        yield
        self.tombstones[d].remove(j)


    @log_start_end_time()
    def generalize_diag(self, s: Solver, prog: Program, f: Iterable[Expr]) -> None:
        if logger.isEnabledFor(logging.DEBUG):
            logger.debug('generalizing diagram')
            logger.debug(str(self))

        i = 0
        for d, j, c in self.conjuncts():
            with self.without(d, j):
                m = check_two_state_implication_all_transitions(s, prog, f, syntax.Not(self.to_ast()))
            if m is None:
                if logger.isEnabledFor(logging.DEBUG):
                    logger.debug('eliminated clause %s' % c)
                self.remove_clause(d, j)


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
        if self.key_old is not None:
            l.append('old state:')
            l.append(Model._state_str(self.old_const_interps, self.old_rel_interps))
            l.append('\nnew state:')
        l.append(Model._state_str(self.const_interps, self.rel_interps))

        return '\n'.join(l)

    @staticmethod
    def _state_str(
            Cs: Dict[ConstantDecl,str],
            Rs: Dict[RelationDecl, List[Tuple[List[str], bool]]]
    ) -> str:
        l = []
        for C in Cs:
            l.append('%s = %s' % (C.name, Cs[C]))

        for R in Rs:

            for tup, b in sorted(Rs[R]):
                l.append('%s%s(%s)' % ('' if b else '!', R.name, ','.join(tup)))

        return '\n'.join(l)

    def read_out(self) -> None:
        # logger.debug('read_out')
        def rename(s: str) -> str:
            return s.replace('!val!', '')

        self.univs: Dict[SortDecl, List[str]] = OrderedDict()
        assert self.prog.scope is not None
        for z3sort in sorted(self.z3model.sorts(), key=str):
            sort = self.prog.scope.get_sort(str(z3sort))
            assert sort is not None
            self.univs[sort] = [rename(str(x)) for x in self.z3model.get_universe(z3sort)]
#            if logger.isEnabledFor(logging.DEBUG):
#                logger.debug(str(z3sort))
#                for x in self.univs[sort]:
#                    logger.debug('  ' + x)


        self.rel_interps: Dict[RelationDecl, List[Tuple[List[str], bool]]] = OrderedDict()
        self.const_interps: Dict[ConstantDecl, str] = OrderedDict()

        if self.key_old is not None:
            self.old_rel_interps: Dict[RelationDecl, List[Tuple[List[str], bool]]] = OrderedDict()
            self.old_const_interps: Dict[ConstantDecl, str] = OrderedDict()

        for z3decl in sorted(self.z3model.decls(), key=str):
            z3name = str(z3decl)
            if z3name.startswith(self.key):
                name = z3name[len(self.key)+1:]
                R: Dict[RelationDecl, List[Tuple[List[str], bool]]] = self.rel_interps
                C: Dict[ConstantDecl, str] = self.const_interps
            elif self.key_old is not None and z3name.startswith(self.key_old):
                name = z3name[len(self.key_old)+1:]
                R = self.old_rel_interps
                C = self.old_const_interps
            else:
                name = z3name
                R = self.rel_interps
                C = self.const_interps


            decl = self.prog.scope.get(name)
            assert not isinstance(decl, syntax.Sort) and \
                not isinstance(decl, syntax.SortInferencePlaceholder)
            if decl is not None:
#                if logger.isEnabledFor(logging.DEBUG):
#                    logger.debug(str(z3decl))
                if isinstance(decl, RelationDecl):
                    if len(decl.arity) > 0:
                        l = []
                        domains = [self.z3model.get_universe(z3decl.domain(i))
                                   for i in range(z3decl.arity())]
                        g = itertools.product(*domains)
                        for row in g:
                            ans = self.z3model.eval(z3decl(*row))
                            l.append(([rename(str(col)) for col in row], bool(ans)))
                        assert decl not in R
                        R[decl] = l
                    else:
                        ans = self.z3model.eval(z3decl())
                        assert decl not in R
                        R[decl] = [([], bool(ans))]
                else:
                    assert isinstance(decl, ConstantDecl)
                    v = self.z3model.eval(z3decl()).decl().name()
                    assert decl not in C
                    C[decl] = rename(v)
            else:
                pass
#                 if logger.isEnabledFor(logging.DEBUG):
#                     logger.debug('extra constant: ' + str(z3decl))

    def as_diagram(self) -> Diagram:
        assert self.key_old is None, 'diagram can only be generated from a 1-state model'
        # TODO: remove above assertion by supporting 2-state models

        vs: List[syntax.SortedVar] = []
        ineqs: Dict[SortDecl, List[Expr]] = OrderedDict()
        rels: Dict[RelationDecl, List[Expr]] = OrderedDict()
        consts: Dict[ConstantDecl, Expr] = OrderedDict()
        for sort in self.univs:
            vs.extend(syntax.SortedVar(None, v, syntax.UninterpretedSort(None, sort.name))
                      for v in self.univs[sort])

            ineqs[sort] = []
            u = [syntax.Id(None, s) for s in self.univs[sort]]
            for i, a in enumerate(u):
                for b in u[i+1:]:
                    ineqs[sort].append(syntax.Neq(a, b))
        for R in self.rel_interps:
            rels[R] = []
            for tup, ans in self.rel_interps[R]:
                e: Expr
                if len(tup) > 0:
                    e = syntax.AppExpr(None, R.name, [syntax.Id(None, col) for col in tup])

                else:
                    e = syntax.Id(None, R.name)
                e = e if ans else syntax.Not(e)
                rels[R].append(e)
        for C in self.const_interps:
            e = syntax.Eq(syntax.Id(None, C.name), syntax.Id(None, self.const_interps[C]))
            consts[C] = e

        diag = Diagram(vs, ineqs, rels, consts)
        assert self.prog.scope is not None
        diag.resolve(self.prog.scope)

        return diag

class Frames(object):
    def __init__(self, solver: Solver, prog: Program, safety: Sequence[Expr]) -> None:
        self.solver = solver
        self.prog = prog
        self.safety = safety
        self.fs: List[MySet[Expr]] = []
        self.push_cache: List[Set[Expr]] = []
        self.counter = 0

        self.new_frame(init.expr for init in prog.inits())

        # safety of initial state is checked before instantiating Frames
        for c in safety:
            self[-1].add(c)

        self.new_frame()



    def __getitem__(self, i: int) -> MySet[Expr]:
        return self.fs[i]

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
        assert args is not None

        for i, f in enumerate(self.fs[:-1]):
            logger.debug('pushing in frame %d' % i)

            frame_old_count = self.counter
            j = 0
            while j < len(f):
                c = f.l[j]
                if c in self[i+1] or c in self.push_cache[i]:
                    j += 1
                    continue

                is_safety = c in self.safety
                conjunct_old_count = self.counter

                while True:
                    if not is_safety and args.convergence_hacks and (
                            self.counter >= conjunct_old_count + 3 or
                            self.counter >= frame_old_count + 10
                        ): # total hack
                        logging.info('decided to give up pushing conjunct %s' % c)
                        break

                    logger.debug('attempting to push %s' % c)
                    m = check_two_state_implication_all_transitions(self.solver, self.prog, f, c)
                    if m is None:
                        logger.debug('managed to push %s' % c)
                        self[i+1].add(c)
                        break
                    else:
                        mod = Model(self.prog, m, 'old')
                        diag = mod.as_diagram()
                        if logger.isEnabledFor(logging.DEBUG):
                            logger.debug('failed to immediately push %s' % c)
                            logger.debug(str(mod))
                        if is_safety:
                            logger.debug('note: current clause is safety condition')
                            self.block(diag, i, [], True)
                        else:
                            if not self.block(diag, i, [], False):
                                break

                self.push_cache[i].add(c)
                j += 1

    def block(
            self,
            diag: Diagram,
            j: int,
            trace: List[Tuple[TransitionDecl,Diagram]]=[],
            safety_goal: bool=True
    ) -> bool:
        assert args is not None

        if j == 0: # or (j == 1 and sat(init and diag)
            if safety_goal:
                print(trace)
                raise Exception('abstract counterexample')
            else:
                if logger.isEnabledFor(logging.DEBUG):
                    logger.debug('failed to block diagram')
                    logger.debug(str(diag))
                return False

        old_count = self.counter

        # print fs
        while True:
            if not safety_goal and args.convergence_hacks and self.counter >= old_count + 3:
                if logger.isEnabledFor(logging.DEBUG):
                    logger.debug('decide to give up blocking diagram in frame %s' % j)
                    logger.debug(str(diag))
                    return False

            if logger.isEnabledFor(logging.DEBUG):
                logger.debug('blocking diagram in frame %s' % j)
                logger.debug(str(diag))

                logger.debug('frame %d is' % (j-1))
                logger.debug('\n'.join(str(x) for x in self[j-1]))
            res, x = self.find_predecessor(self[j-1], diag)
            if res == z3.unsat:
                logger.debug('no predecessor: blocked!')
                assert isinstance(x, MySet)
                core: MySet[int] = x
                break
            assert isinstance(x, tuple), (res, x)
            trans, pre_diag = x

            trace.append(x)
            if not self.block(pre_diag, j-1, trace, safety_goal):
                return False
            trace.pop()

        if logger.isEnabledFor(logging.DEBUG):
            logger.debug('core')
            logger.debug(str(core))

            logger.debug('unminimized diag')
            logger.debug(str(diag))

        diag.minimize_from_core(core)
        diag.generalize_diag(self.solver, self.prog, self[j-1])

        e = syntax.Not(diag.to_ast())

        if logger.isEnabledFor(logging.DEBUG):
            logger.debug('adding new clause to frames 0 through %d' % j)
            logger.debug(str(e))

        self.add(e, j)

        return True


    def add(self, e: Expr, j: Optional[int]=None) -> None:
        self.counter += 1

        if j is None:
            j = len(self)
        for i in range(j+1):
            self[i].add(e)


    def find_predecessor(
            self,
            pre_frame: Iterable[Expr],
            diag: Diagram
    ) -> Tuple[z3.CheckSatResult, Union[MySet[int], Tuple[TransitionDecl, Diagram]]]:

        assert args is not None
        if args.use_z3_unsat_cores:
            core: MySet[int] = MySet()

        t = self.solver.get_translator('new', 'old')

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
                        m = Model(self.prog, self.solver.model(), 'old')
                        if logger.isEnabledFor(logging.DEBUG):
                            logger.debug(str(m))
                        return (res, (trans, m.as_diagram()))
                    elif args.use_z3_unsat_cores:
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

        if not args.use_z3_unsat_cores:
            core = MySet([i for i in range(len(diag.trackers))])
        else:
            core = MySet(sorted(core))

        return (z3.unsat, core)

    def simplify(self) -> None:
        for i, f in enumerate(self.fs):
            logger.debug('simplifying frame %d' % i)
            l = []
            for c in reversed(f.l):
                f_minus_c = [x for x in f.l if x in f.s and x is not c]
                if c not in self.safety and \
                   check_implication(self.solver, f_minus_c, [c]) is None:
                    logging.debug('removed %s' % c)
                    f.s.remove(c)
                else:
                    l.append(c)
            f.l = l



    def search(self) -> MySet[Expr]:
        while True:
            f: Optional[OrderedSet[Expr]]
            for i, f in enumerate(self.fs):
                logger.info('frame %d is\n%s' % (i, '\n'.join(str(x) for x in f)))
                logger.info('')

            logger.info('considering frame %s' % (len(self) - 1,))

            f = self.get_inductive_frame()
            if f is not None:
                print('frame is safe and inductive. done!')
                print('\n'.join(str(x) for x in f))
                return f

            logger.info('frame is safe but not inductive. starting new frame')
            self.new_frame()

@log_start_end_time(logging.INFO)
def updr(s: Solver, prog: Program) -> None:
    assert prog.scope is not None

    check_init(s, prog)

    assert args is not None
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

    fs = Frames(s, prog, safety)
    fs.search()

def debug_tokens(filename: str) -> None:
    with open(filename) as f:
        parser.lexer.input(f.read())

    while True:
        tok = parser.lexer.token()
        if not tok: 
            break      # No more input
        print(tok)

@log_start_end_time(logging.INFO)
def verify(s: Solver, prog: Program) -> None:
    check_init(s, prog)
    check_transitions(s, prog)

    print('all ok!')

def parse_args() -> argparse.Namespace:
    argparser = argparse.ArgumentParser()

    subparsers = argparser.add_subparsers()

    verify_subparser = subparsers.add_parser('verify')
    verify_subparser.set_defaults(main=verify)

    updr_subparser = subparsers.add_parser('updr')
    updr_subparser.set_defaults(main=updr)

    for s in [verify_subparser, updr_subparser]:
        s.add_argument('--log', default='WARNING')
        s.add_argument('--log-time', action='store_true')
        s.add_argument('--seed', type=int, default=0)

    updr_subparser.add_argument('--safety')
    updr_subparser.add_argument('--use-z3-unsat-cores', action='store_true')
    updr_subparser.add_argument('--convergence-hacks', action='store_true')

    argparser.add_argument('filename')

    return argparser.parse_args()

def main() -> None:
    global args
    args = parse_args()

    if args.log_time:
        fmt = '%(levelname)s %(asctime)s %(filename)s:%(lineno)d: %(message)s'
    else:
        fmt = '%(levelname)s %(filename)s:%(lineno)d: %(message)s'

    logging.basicConfig(format=fmt, level=getattr(logging, args.log.upper(), None), stream=sys.stdout)

    logger.info('setting seed to %d' % args.seed)
    z3.set_param('smt.random_seed', args.seed)

    with open(args.filename) as f:
        prog: syntax.Program = parser.program_parser.parse(input=f.read(), filename=args.filename)

    prog.resolve()

    scope = prog.scope
    assert scope is not None
    assert len(scope.stack) == 0

    s = Solver(cast(Scope[z3.ExprRef], scope))
    t = s.get_translator()
    for a in prog.axioms():
        s.add(t.translate_expr(a.expr))

    args.main(s, prog)

if __name__ == '__main__':
    main()
