#!/usr/bin/env python3.7

from __future__ import annotations
import argparse
from collections import OrderedDict, defaultdict
from contextlib import contextmanager
import copy
from datetime import datetime
import io
import itertools
import logging
import sys
from typing import List, Any, Optional, Callable, Set, Tuple, Union, Iterable, \
    Dict, TypeVar, Sequence, Iterator, cast
import z3

import parser
import syntax
from syntax import Expr, Program, Scope, ConstantDecl, RelationDecl, SortDecl, \
    FunctionDecl, DefinitionDecl, InvariantDecl, AutomatonDecl
import utils
from utils import MySet

from phases import PhaseAutomaton, Phase, Frame, PhaseTransition

import pd

_logger = utils.MyLogger(logging.getLogger(__file__), datetime.now())

z3.Forall = z3.ForAll

KEY_ONE = 'one'
KEY_NEW = 'new'
KEY_OLD = 'old'
TRANSITION_INDICATOR = 'tid'

class Solver(object):
    def __init__(self, scope: Scope[z3.ExprRef]) -> None:
        self.z3solver = z3.Solver()
        self.scope = scope
        self.translators: Dict[Tuple[Optional[str], Optional[str]], syntax.Z3Translator] = {}
        self.nqueries = 0
        self.assumptions_necessary = False
        self.known_keys: Set[str] = set()
        self.mutable_axioms: List[Expr] = []

    def register_mutable_axioms(self, axioms: Iterable[Expr]) -> None:
        assert len(self.known_keys) == 0, "mutable axioms must be registered before any keys are known to the solver!"
        self.mutable_axioms.extend(axioms)

    def _initialize_key(self, key: Optional[str]) -> None:
        if key is not None and key not in self.known_keys:
            self.known_keys.add(key)

            assert self.z3solver.num_scopes() == 0, "the first time get_translator is called with a particular key, there must be no scopes pushed on the Z3 stack!"

            t = self.get_translator(key)
            for a in self.mutable_axioms:
                self.add(t.translate_expr(a))

    def get_translator(self, key: Optional[str]=None, key_old: Optional[str]=None) \
        -> syntax.Z3Translator:
        t = (key, key_old)
        if t not in self.translators:
            self._initialize_key(key)
            self._initialize_key(key_old)
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
        if utils.args.minimize_models:
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

    def _relational_cardinality_constraint(self, d: z3.FuncDeclRef, n: int) -> z3.ExprRef:
        assert d.arity() == 1 and n == 1

        s = d.domain(0)

        x, y = z3.Consts('x y', s)

        return z3.Forall([x, y], z3.Implies(z3.And(d(x), d(y)), x == y))

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

            for d in m.decls():
                nm = d.name()
                if nm.startswith(KEY_OLD) or nm.startswith(KEY_ONE):
                    arity = d.arity()
                    if arity == 1 and d.range() == z3.BoolSort():
                        s = d.domain(0)
                        u = m.get_universe(s)
                        hi = sum(1 if m.eval(d(x)) else 0 for x in u)
                        n = 1
                        while n < hi and n < 2:  # hehe
                            with self:
                                self.add(self._relational_cardinality_constraint(d, n))
                                res = self.check(assumptions)
                                if res == z3.sat:
                                    break
                            n += 1
                        if n < hi and n < 2:
                            self.add(self._relational_cardinality_constraint(d, n))

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

    def reason_unknown(self) -> str:
        return self.z3solver.reason_unknown()


T = TypeVar('T')

def check_unsat(
        errmsgs: List[Tuple[Optional[syntax.Token], str]],
        s: Solver,
        prog: Program,
        keys: List[str]
) -> z3.CheckSatResult:
    start = datetime.now()
    # if logger.isEnabledFor(logging.DEBUG):
    #     logger.debug('assertions')
    #     logger.debug(str(s.assertions()))

    res = s.check()
    if res != z3.unsat:
        if res == z3.sat:
            m = Model(prog, s.model(), s, keys)

            _logger.always_print('')
            _logger.always_print(str(m))
        else:
            assert res == z3.unknown
            _logger.always_print('unknown!')
            _logger.always_print('reason unknown: ' + s.reason_unknown())
        for tok, msg in errmsgs:
            utils.print_error(tok, msg)
    else:
        _logger.always_print('ok. (%s)' % (datetime.now() - start))
        sys.stdout.flush()

    return res

@utils.log_start_end_xml(_logger, logging.INFO)
def check_init(s: Solver, prog: Program, safety_only: bool=False) -> None:
    _logger.always_print('checking init:')

    t = s.get_translator(KEY_ONE)

    with s:
        for init in prog.inits():
            s.add(t.translate_expr(init.expr))

        for inv in (prog.invs() if not safety_only else prog.safeties()):
            with s:
                s.add(z3.Not(t.translate_expr(inv.expr)))

                if inv.name is not None:
                    msg = ' ' + inv.name
                elif inv.tok is not None:
                    msg = ' on line %d' % inv.tok.lineno
                else:
                    msg = ''
                _logger.always_print('  implies invariant%s... ' % msg, end='')
                sys.stdout.flush()

                check_unsat([(inv.tok, 'invariant%s may not hold in initial state' % msg)], s, prog, [KEY_ONE])


def check_transitions(s: Solver, prog: Program) -> None:
    t = s.get_translator(KEY_NEW, KEY_OLD)

    with s:
        for inv in prog.invs():
            s.add(t.translate_expr(inv.expr, old=True))

        for trans in prog.transitions():
            if utils.args.check_transition is not None and trans.name not in utils.args.check_transition:
                continue

            _logger.always_print('checking transation %s:' % (trans.name,))

            with s:
                s.add(t.translate_transition(trans))
                for inv in prog.invs():
                    if utils.args.check_invariant is not None and \
                       inv.name not in utils.args.check_invariant:
                        continue

                    with s:
                        s.add(z3.Not(t.translate_expr(inv.expr)))

                        if inv.name is not None:
                            msg = ' ' + inv.name
                        elif inv.tok is not None:
                            msg = ' on line %d' % inv.tok.lineno
                        else:
                            msg = ''
                        _logger.always_print('  preserves invariant%s... ' % msg, end='')
                        sys.stdout.flush()

                        check_unsat([(inv.tok, 'invariant%s may not be preserved by transition %s' %
                                      (msg, trans.name)),
                                     (trans.tok, 'this transition may not preserve invariant%s' % (msg,))],
                                    s, prog, [KEY_OLD, KEY_NEW])

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
                # if _logger.isEnabledFor(logging.DEBUG):
                #     _logger.debug('assertions')
                #     _logger.debug(str(s.assertions()))

                if s.check() != z3.unsat:
                    return s.model()

    return None

def check_two_state_implication_all_transitions(
        s: Solver,
        prog: Program,
        old_hyps: Iterable[Expr],
        new_conc: Expr
) -> Optional[Tuple[z3.ModelRef, DefinitionDecl]]:
    t = s.get_translator(KEY_NEW, KEY_OLD)
    with s:
        for h in old_hyps:
            s.add(t.translate_expr(h, old=True))

        s.add(z3.Not(t.translate_expr(new_conc)))

        for trans in prog.transitions():
            with s:
                s.add(t.translate_transition(trans))

                # if _logger.isEnabledFor(logging.DEBUG):
                #     _logger.debug('assertions')
                #     _logger.debug(str(s.assertions()))

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
            #_logger.debug("two state implication check post %s; transition %s; pre %s" % (new_conc, phase_transition, old_hyps))
            delta = phase_transition.transition_decl()
            trans = prog.scope.get_definition(delta.transition)
            assert trans is not None
            precond = delta.precond

            with s:
                s.add(t.translate_transition(trans, precond=precond))

                # if _logger.isEnabledFor(logging.DEBUG):
                #     _logger.debug('assertions')
                #     _logger.debug(str(s.assertions()))

                if s.check() != z3.unsat:
                    #_logger.debug("two state implication check invalid")
                    return s.model(), phase_transition
            #_logger.debug("two state implication check valid")

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
        self.tombstones: Dict[Union[SortDecl, RelationDecl, ConstantDecl, FunctionDecl], Optional[Set[int]]] = \
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
        if utils.args.simple_conjuncts:
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
        if utils.args.smoke_test and depth is not None:
            _logger.debug('smoke testing at depth %s...' % (depth,))
            _logger.debug(str(self))
            check_bmc(s, prog, syntax.Not(self.to_ast()), depth)

    # TODO: merge similarities with clause_implied_by_transitions_from_frame...
    def check_valid_in_phase_from_frame(self, s: Solver, prog: Program, f: Frame,
                                        transitions_to_grouped_by_src: Dict[Phase, Sequence[PhaseTransition]],
                                        propagate_init: bool) \
    -> Optional[z3.ModelRef]:
        for src, transitions in transitions_to_grouped_by_src.items():
            # _logger.debug("gen: check transition from %s by %s" % (src.name(), str(list(transitions))))
            ans = check_two_state_implication_along_transitions(s, prog, f.summary_of(src), transitions,
                                                                syntax.Not(self.to_ast()))
            if ans is not None:
                return ans[0]

        if propagate_init:
            return self.valid_in_init(s, prog)
        return None

    @utils.log_start_end_xml(_logger)
    @utils.log_start_end_time(_logger)
    def generalize(self, s: Solver, prog: Program, f: Frame,
                   transitions_to_grouped_by_src: Dict[Phase, Sequence[PhaseTransition]],
                   propagate_init: bool,
                   depth: Optional[int]=None) -> None:
        if _logger.isEnabledFor(logging.DEBUG):
            _logger.debug('generalizing diagram')
            _logger.debug(str(self))
            with utils.LogTag(_logger, 'previous-frame', lvl=logging.DEBUG):
                for p in f.phases():
                    _logger.log_list(logging.DEBUG, ['previous frame for %s is' % p.name()] + [str(x) for x in f.summary_of(p)])

        T = Union[SortDecl, RelationDecl, ConstantDecl, FunctionDecl]
        d: T
        I: Iterable[T] = self.ineqs
        R: Iterable[T] = self.rels
        C: Iterable[T] = self.consts
        F: Iterable[T] = self.funcs

#         if _logger.isEnabledFor(logging.DEBUG):
#             _logger.debug('checking that transition relation itself is SAT from previous frame...')
#             res1 = check_two_state_implication_all_transitions(s, prog, f, syntax.Bool(None, False))
#             if res1 is None:
#                 assert False
#             m, t = res1
#             _logger.always_print(str(m))
#             _logger.always_print(t.name)

        self.smoke(s, prog, depth)

        with utils.LogTag(_logger, 'eliminating-conjuncts', lvl=logging.DEBUG):
            for d in itertools.chain(I, R, C, F):
                if isinstance(d, SortDecl) and len(self.ineqs[d]) == 1:
                    continue
                with self.without(d):
                    res = self.check_valid_in_phase_from_frame(s, prog, f, transitions_to_grouped_by_src, propagate_init)
                if res is None:
                    if _logger.isEnabledFor(logging.DEBUG):
                        _logger.debug('eliminated all conjuncts from declaration %s' % d)
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
                        if _logger.isEnabledFor(logging.DEBUG):
                            _logger.debug('eliminated all negative conjuncts from declaration %s' % d)
                        self.remove_clause(d, cs)
                        self.smoke(s, prog, depth)

            for d, j, c in self.conjuncts():
                with self.without(d, j):
                    res = self.check_valid_in_phase_from_frame(s, prog, f, transitions_to_grouped_by_src, propagate_init)
                if res is None:
                    if _logger.isEnabledFor(logging.DEBUG):
                        _logger.debug('eliminated clause %s' % c)
                    self.remove_clause(d, j)
                    self.smoke(s, prog, depth)
    #            elif _logger.isEnabledFor(logging.DEBUG):
    #
    #                _logger.debug('failed to eliminate clause %s' % c)
    #                _logger.debug('from diagram %s' % self)
    #
    #                if isinstance(res, tuple):
    #                    m, t = res
    #                    _logger.debug('because of transition %s' % t.name)
    #                    _logger.debug('and model %s' % Model(prog, m, KEY_NEW, KEY_OLD))
    #                else:
    #                    _logger.debug('because the diagram is satisfiable in the initial state')
    #                    _logger.debug('and model %s' % Model(prog, m, KEY_ONE))



        self.prune_unused_vars()

        if _logger.isEnabledFor(logging.DEBUG):
            _logger.debug('generalized diag')
            _logger.debug(str(self))

def log_diagram(diag: Diagram, lvl: int=logging.DEBUG) -> None:
    _logger.log(lvl, str(diag))

class Model(object):
    def __init__(
            self,
            prog: Program,
            m: z3.ModelRef,
            solver: Solver,
            keys: List[str],
    ) -> None:
        self.prog = prog
        self.z3model = m
        self.keys = keys
        self.solver = solver

        self.read_out()

    def try_printed_by(self, s: SortDecl, elt: str) -> Optional[str]:
        custom_printer_annotation = syntax.get_annotation(s, 'printed_by')

        if custom_printer_annotation is not None:
            assert len(custom_printer_annotation.args) >= 1
            import importlib
            printers = importlib.import_module('printers')
            printer_name = custom_printer_annotation.args[0]
            custom_printer = printers.__dict__.get(printer_name)
            custom_printer_args = custom_printer_annotation.args[1:] if custom_printer is not None else []
            if custom_printer is not None:
                return custom_printer(self, s, elt, custom_printer_args)
            else:
                utils.print_warning(custom_printer_annotation.tok, 'could not find printer named %s' % (printer_name,))
        return None

    def print_element(self, s: Union[SortDecl, syntax.Sort], elt: str) -> str:
        if not isinstance(s, SortDecl):
            assert isinstance(s, syntax.UninterpretedSort) and s.decl is not None
            s = s.decl

        return self.try_printed_by(s, elt) or elt

    def print_tuple(self, arity: List[syntax.Sort], tup: List[str]) -> str:
        l = []
        assert len(arity) == len(tup)
        for s, x in zip(arity, tup):
            l.append(self.print_element(s, x))
        return ','.join(l)

    def univ_str(self) -> List[str]:
        l = []
        for s in sorted(self.univs.keys(), key=str):
            l.append(str(s))
            for x in sorted(self.univs[s], key=lambda x: self.print_element(s, x)):
                l.append('  %s' % self.print_element(s, x))
        return l

    def __str__(self) -> str:
        l = []
        l.extend(self.univ_str())
        l.append(self._state_str(self.immut_const_interps, self.immut_rel_interps, self.immut_func_interps))
        for i, k in enumerate(self.keys):
            if i > 0 and self.transitions[i-1] != '':
                l.append('\ntransition %s' % (self.transitions[i-1],))
            l.append('\nstate %s:' % (i,))
            l.append(self._state_str(self.const_interps[i], self.rel_interps[i], self.func_interps[i]))

        return '\n'.join(l)

    def _state_str(
            self,
            Cs: Dict[ConstantDecl,str],
            Rs: Dict[RelationDecl, List[Tuple[List[str], bool]]],
            Fs: Dict[FunctionDecl, List[Tuple[List[str], str]]]
    ) -> str:
        l = []
        for C in Cs:
            if syntax.has_annotation(C,'no_print'):
                continue
            l.append('%s = %s' % (C.name, self.print_element(C.sort, Cs[C])))

        for R in Rs:
            if syntax.has_annotation(R,'no_print'):
                continue
            for tup, b in sorted(Rs[R], key=lambda x: self.print_tuple(R.arity, x[0])):
                if b:
                    l.append('%s%s(%s)' % ('' if b else '!', R.name, self.print_tuple(R.arity, tup)))

        for F in Fs:
            if syntax.has_annotation(F,'no_print'):
                continue
            for tup, res in sorted(Fs[F], key=lambda x: self.print_tuple(F.arity, x[0])):
                l.append('%s(%s) = %s' % (F.name, self.print_tuple(F.arity, tup), self.print_element(F.sort, res)))

        return '\n'.join(l)


    def _eval(self, expr: z3.ExprRef) -> z3.ExprRef:
        ans = self.z3model.eval(expr, model_completion=True)
        assert ans == True or ans == False, (expr, ans)
        return ans

    def read_out(self) -> None:
        # _logger.debug('read_out')
        def rename(s: str) -> str:
            return s.replace('!val!', '')

        self.univs: Dict[SortDecl, List[str]] = OrderedDict()
        for z3sort in sorted(self.z3model.sorts(), key=str):
            sort = self.prog.scope.get_sort(str(z3sort))
            assert sort is not None
            self.univs[sort] = list(sorted(rename(str(x)) for x in self.z3model.get_universe(z3sort)))
            # if _logger.isEnabledFor(logging.DEBUG):
            #     _logger.debug(str(z3sort))
            #     for x in self.univs[sort]:
            #         _logger.debug('  ' + x)


        RT = Dict[RelationDecl, List[Tuple[List[str], bool]]]
        CT = Dict[ConstantDecl, str]
        FT = Dict[FunctionDecl, List[Tuple[List[str], str]]]

        self.immut_rel_interps: RT = OrderedDict()
        self.immut_const_interps: CT = OrderedDict()
        self.immut_func_interps: FT = OrderedDict()

        self.rel_interps: List[RT] = [OrderedDict() for i in range(len(self.keys))]
        self.const_interps: List[CT] = [OrderedDict() for i in range(len(self.keys))]
        self.func_interps: List[FT] = [OrderedDict() for i in range(len(self.keys))]

        self.transitions: List[str] = ['' for i in range(len(self.keys) - 1)]

        model_decls = self.z3model.decls()
        all_decls = model_decls
        for z3decl in sorted(all_decls, key=str):
            z3name = str(z3decl)
            for i, k in enumerate(self.keys):
                if z3name.startswith(k):
                    name = z3name[len(k + '_'):]
                    R: RT = self.rel_interps[i]
                    C: CT = self.const_interps[i]
                    F: FT = self.func_interps[i]
                    break
            else:
                name = z3name
                R = self.immut_rel_interps
                C = self.immut_const_interps
                F = self.immut_func_interps

            decl = self.prog.scope.get(name)
            assert not isinstance(decl, syntax.Sort) and \
                not isinstance(decl, syntax.SortInferencePlaceholder)
            if decl is not None:
#                if _logger.isEnabledFor(logging.DEBUG):
#                    _logger.debug(str(z3decl))
                if isinstance(decl, RelationDecl):
                    if len(decl.arity) > 0:
                        rl = []
                        domains = [self.z3model.get_universe(z3decl.domain(i))
                                   for i in range(z3decl.arity())]
                        if not any(x is None for x in domains):
                            # Note: if any domain is None, we silently drop this symbol.
                            # It's not entirely clear that this is an ok thing to do.
                            g = itertools.product(*domains)
                            for row in g:
                                relation_expr = z3decl(*row)
                                ans = self._eval(relation_expr)
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
                    if not any(x is None for x in domains):
                        # Note: if any domain is None, we silently drop this symbol.
                        # It's not entirely clear that this is an ok thing to do.
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
#                 if _logger.isEnabledFor(logging.DEBUG):
#                     _logger.debug('extra constant: ' + str(z3decl))
                if name.startswith(TRANSITION_INDICATOR + '_') and self.z3model.eval(z3decl()):
                    name = name[len(TRANSITION_INDICATOR + '_'):]
                    istr, name = name.split('_', maxsplit=1)
                    i = int(istr)
                    self.transitions[i] = name

    def as_diagram(self, i: Optional[int]=None) -> Diagram:
        assert len(self.keys) == 1 or i is not None, 'to generate a diagram from a multi-state model, you must specify which state you want'
        assert i is None or (0 <= i and i < len(self.keys))

        if i is None:
            i = 0

        mut_rel_interps = self.rel_interps[i]
        mut_const_interps = self.const_interps[i]
        mut_func_interps = self.func_interps[i]

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
        if utils.args.simplify_diagram:
            diag.simplify_consts()
        assert self.prog.scope is not None
        diag.resolve(self.prog.scope)

        return diag

    def as_onestate_formula(self, i: Optional[int]=None) -> Expr:
        pass

class Blocked(object):
    pass
class CexFound(object):
    pass
class GaveUp(object):
    pass


def phase_safety(p: Phase) -> Sequence[InvariantDecl]:
    if utils.args.sketch:
        return p.safety + p.sketch_invs
    return p.safety

def verbose_print_z3_model(m: z3.ModelRef) -> None:
    _logger.always_print('')
    out = io.StringIO()
    fmt = z3.Formatter() # type: ignore
    fmt.max_args = 10000
    _logger.always_print(str(fmt.max_args))
    pp = z3.PP() # type: ignore
    pp.max_lines = 10000
    pp(out, fmt(m))
    _logger.always_print(out.getvalue())
    assert False



class Frames(object):
    @utils.log_start_end_xml(_logger, logging.DEBUG, 'Frames.__init__')
    def __init__(self, solver: Solver, prog: Program) -> None:
        self.solver = solver
        self.prog = prog

        if utils.args.automaton:
            automaton = prog.the_automaton()
            if automaton is None:
                utils.print_error_and_exit(None, 'updr --automaton requires the file to declare an automaton')
        else:
            the_phase = 'the_phase'
            pcs: List[syntax.PhaseComponent] = []
            for t in self.prog.transitions():
                pcs.append(syntax.PhaseTransitionDecl(None, t.name, None, the_phase))
            for inv in self.prog.safeties():
                pcs.append(inv)

            automaton = AutomatonDecl(None, [syntax.InitPhaseDecl(None, the_phase),
                                             syntax.PhaseDecl(None, the_phase, pcs)])

            automaton.resolve(prog.scope)

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
        _logger.debug("new frame! %s" % len(self.fs))
        self.fs.append(Frame(self.automaton.phases(), contents))
        self.push_cache.append({p: set() for p in self.automaton.phases()})

        self.push_forward_frames()

        with utils.LogTag(_logger, 'current-frames-after-push', lvl=logging.DEBUG):
            self.print_frames(lvl=logging.DEBUG)

        self.establish_safety()

        with utils.LogTag(_logger, 'current-frames-after-safety', lvl=logging.DEBUG):
            self.print_frames(lvl=logging.DEBUG)

        self.simplify()

        with utils.LogTag(_logger, 'current-frames-after-simplify', lvl=logging.DEBUG):
            self.print_frames(lvl=logging.DEBUG)



    @utils.log_start_end_xml(_logger)
    def establish_safety(self) -> None:
        self.assert_inductive_trace()

        frame_no = len(self.fs) - 1

        while True:
            with utils.LogTag(_logger, 'establish-safety-attempt'):
                res = self._get_some_cex_to_safety()

                if res is None:
                    break

                (violating, diag) = res
                self.block(diag, frame_no, violating, [(None, diag)], True)

        self.assert_inductive_trace()

    def _get_some_cex_to_safety(self) -> Optional[Tuple[Phase, Diagram]]:
        f = self.fs[-1]

        def safety_property_checker(p: Phase) -> Optional[Tuple[Phase, Diagram]]:
            res = check_implication(self.solver, f.summary_of(p), (inv.expr for inv in phase_safety(p)))

            if res is None:
                _logger.debug("Frontier frame phase %s implies safety, summary is %s" % (p.name(), f.summary_of(p)))
                return None

            _logger.debug("Frontier frame phase %s cex to safety" % p.name())
            z3m: z3.ModelRef = res
            mod = Model(self.prog, z3m, self.solver, [KEY_ONE])
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
                        _logger.debug('transition %s is covered trivially by %s' % (trans.name, p.name()))
                        continue

                    _logger.debug('checking transition %s is covered by %s' % (trans.name, p.name()))

                    with self.solver:
                        self.solver.add(t.translate_transition(trans))
                        self.solver.add(z3.And(*(z3.Not(t.translate_precond_of_transition(delta.precond(), trans))
                                       for delta in edges_from_phase_matching_prog_trans)))

                        if self.solver.check() != z3.unsat:
                            _logger.debug('phase %s cex to edge covering of transition %s' % (p.name(), trans.name))
                            z3m: z3.ModelRef = self.solver.model()
                            mod = Model(self.prog, z3m, self.solver, [KEY_OLD, KEY_NEW])
                            diag = mod.as_diagram(i=0)
                            return (p, diag)

                        _logger.debug('transition %s is covered non-trivially by %s' % (trans.name, p.name()))
                        continue

                _logger.debug('all edges covered from phase %s' % p.name())
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
        is_safety = c in phase_safety(p)

        f = self.fs[frame_no]
        while True:
            with utils.LogTag(_logger, 'pushing-conjunct-attempt', lvl=logging.DEBUG, frame=str(frame_no), conj=str(c)):
                _logger.debug('frame %s phase %s attempting to push %s' % (frame_no, p.name(), c))

                res = self.clause_implied_by_transitions_from_frame(f, p, c)
                if res is None:
                    _logger.debug('frame %s phase %s managed to push %s' % (frame_no, p.name(), c))

                    if utils.args.smoke_test and _logger.isEnabledFor(logging.DEBUG):
                        _logger.debug('jrw smoke testing...')
                        # TODO: phases
                        check_bmc(self.solver, self.prog, c, frame_no + 1)

                    # assert self.clause_implied_by_transitions_from_frame(f, p, c) is None
                    self[frame_no + 1].strengthen(p, c)
                    self.assert_inductive_trace()
                    break

                pre_phase, (m, t) = res
                mod = Model(self.prog, m, self.solver, [KEY_OLD, KEY_NEW])
                diag = mod.as_diagram(i=0)

                if _logger.isEnabledFor(logging.DEBUG):
                    _logger.debug('frame %s failed to immediately push %s due to transition %s' % (frame_no, c, t.pp()))
                    # _logger.debug(str(mod))
                if is_safety:
                    _logger.debug('note: current clause is safety condition')
                    self.block(diag, frame_no, pre_phase, [(None, c), (t, diag)], safety_goal=True)
                else:
                    if utils.args.block_may_cexs:
                        ans = self.block(diag, frame_no, pre_phase, [(None, c), (t, diag)], safety_goal=False)
                        if isinstance(ans, CexFound):
                            break
                    else:
                        break

    @utils.log_start_end_xml(_logger, logging.DEBUG)
    def push_forward_frames(self) -> None:
        self.assert_inductive_trace()
        for i, f in enumerate(self.fs[:-1]):
            if ((utils.args.push_frame_zero == 'if_trivial' and self.automaton.nontrivial) or \
                (utils.args.push_frame_zero == 'never')) and i == 0:
                continue
            with utils.LogTag(_logger, 'pushing-frame', lvl=logging.DEBUG, i=str(i)):
                for p in self.automaton.phases():
                    _logger.debug('pushing in frame %d phase %s' % (i, p.name()))
                    self.push_phase_from_pred(i, f, p)
                    # self.assert_inductive_trace()

        self.assert_inductive_trace()

    def assert_inductive_trace(self) -> None:
        if not utils.args.assert_inductive_trace:
            return

        for i, f in enumerate(self.fs[:-1]):
            with utils.LogTag(_logger, 'inductive-trace-assert', lvl=logging.DEBUG, i=str(i)):
                for p in self.automaton.phases():
                    for c in self.fs[i+1].summary_of(p):
                        res = self.clause_implied_by_transitions_from_frame(f, p, c, self._fresh_solver())
                        assert res is None, "Non inductive trace:\n\t%s\n\t%s\n\t%s" % (p.name(), c, f)

    def push_phase_from_pred(self, i: int, f: Frame, p: Phase) -> None:
        frame_old_count = self.counter

        def process_conjunct(c: Expr) -> None:
            if c in self.fs[i+1].summary_of(p) or c in self.push_cache[i][p]:
                return

            with utils.LogTag(_logger, 'pushing-conjunct', lvl=logging.DEBUG, frame=str(i), conj=str(c)):
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
    @utils.log_start_end_xml(_logger, lvl=logging.DEBUG)
    def block(
            self,
            diag: Diagram,
            j: int,
            p: Phase,
            trace: Optional[List[Tuple[Optional[PhaseTransition],Union[Diagram, Expr]]]]=None,
            safety_goal: bool=True
    ) -> Union[Blocked, CexFound]:
        if trace is None:
            trace = []
        if j == 0 or (j == 1 and self.valid_in_initial_frame(self.solver, p, diag) is not None):
            if safety_goal:
                _logger.always_print('\n'.join(((t.pp() + ' ') if t is not None else '') + str(diag) for t, diag in trace))
                raise Exception('abstract counterexample')
            else:
                if _logger.isEnabledFor(logging.DEBUG):
                    _logger.debug('failed to block diagram')
                    # _logger.debug(str(diag))
                return CexFound()

        # print fs
        while True:
            if _logger.isEnabledFor(logging.DEBUG):
                _logger.debug('blocking diagram in frame %s' % j)
                log_diagram(diag, lvl=logging.DEBUG)

                self.print_frame(j-1, lvl=logging.DEBUG)
            res, x = self.find_predecessor(self[j-1], p, diag)
            if res == z3.unsat:
                _logger.debug('no predecessor: blocked!')
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

        if _logger.isEnabledFor(logging.DEBUG) and core is not None:
            _logger.debug('core %s' % core)
            _logger.debug('unminimized diag\n%s' % diag)

        diag.minimize_from_core(core)
        diag.generalize(self.solver, self.prog,
                        self[j-1], self.automaton.transitions_to_grouped_by_src(p), p == self.automaton.init_phase(),
                        j)

        e = syntax.Not(diag.to_ast())

        if _logger.isEnabledFor(logging.DEBUG):
            _logger.debug('adding new clause to frames 0 through %d phase %s' % (j, p.name()))
        if _logger.isEnabledFor(logging.INFO):
            _logger.info("[%d] %s" % (j, str(e)))

        # assert self.clause_implied_by_transitions_from_frame(self.fs[j-1], p, syntax.Not(diag.to_ast())) is None
        self.add(p, e, j)
        _logger.debug("Done blocking")

        return Blocked()

    def valid_in_initial_frame(self, s: Solver, p: Phase, diag: Diagram) -> Optional[z3.ModelRef]:
        return check_implication(s, self.fs[0].summary_of(p), [syntax.Not(diag.to_ast())])


    def augment_core_for_init(self, p: Phase, diag: Diagram, core: Optional[MySet[int]]) -> None:
        if core is None or not utils.args.use_z3_unsat_cores:
            return

        t = self.solver.get_translator(KEY_ONE)

        with self.solver:
            for init in self.fs[0].summary_of(p):
                self.solver.add(t.translate_expr(init))

            self.solver.add(diag.to_z3(t))

            res = self.solver.check(diag.trackers)

            assert res == z3.unsat
            uc = self.solver.unsat_core()
            # if _logger.isEnabledFor(logging.DEBUG):
            #     _logger.debug('uc')
            #     _logger.debug(str(sorted(uc, key=lambda y: y.decl().name())))

                # _logger.debug('assertions')
                # _logger.debug(str(self.solver.assertions()))

            res = self.solver.check([diag.trackers[i] for i in core])
            if res == z3.unsat:
                _logger.debug('augment_core_for_init: existing core sufficient')
                return

            for x in sorted(uc, key=lambda y: y.decl().name()):
                assert isinstance(x, z3.ExprRef)
                core.add(int(x.decl().name()[1:]))
            if _logger.isEnabledFor(logging.DEBUG):
                _logger.debug('augment_core_for_init: new core')
                _logger.debug(str(sorted(core)))

    def add(self, p: Phase, e: Expr, depth: Optional[int]=None) -> None:
        self.counter += 1

        if depth is None:
            depth = len(self)

        if utils.args.smoke_test and _logger.isEnabledFor(logging.DEBUG):
            _logger.debug('smoke testing at depth %s...' % (depth,))
            check_bmc(self.solver, self.prog, e, depth)

        self.assert_inductive_trace()
        for i in range(depth+1):
            self[i].strengthen(p, e)
            _logger.debug("%d %s %s" % (i, p.name(), e))
            self.assert_inductive_trace()
        self.assert_inductive_trace()

    @utils.log_start_end_xml(_logger, lvl=logging.DEBUG)
    def find_predecessor(
            self,
            pre_frame: Frame,
            current_phase: Phase,
            diag: Diagram
    ) -> Tuple[z3.CheckSatResult, Union[Optional[MySet[int]], Tuple[PhaseTransition, Tuple[Phase, Diagram]]]]:
        t = self.solver.get_translator(KEY_NEW, KEY_OLD)

        if utils.args.use_z3_unsat_cores:
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
                    _logger.debug("check predecessor of %s from %s by %s" % (current_phase.name(), src.name(), transitions))
                    (sat_res, pre_diag) = self.find_predecessor_from_src_phase(t, pre_frame, src, transitions, diag, core)
                    if sat_res == z3.unsat:
                        continue
                    return (sat_res, pre_diag)

                if utils.args.use_z3_unsat_cores:
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
                    trans = self.prog.scope.get_definition(delta.transition)
                    assert trans is not None
                    precond = delta.precond

                    with solver:
                        solver.add(t.translate_transition(trans, precond=precond))
                        res = solver.check(diag.trackers)

                        if res != z3.unsat:
                            _logger.debug('found predecessor via %s' % trans.name)
                            m = Model(self.prog, solver.model(diag.trackers), self.solver, [KEY_OLD, KEY_NEW])
                            # if _logger.isEnabledFor(logging.DEBUG):
                            #     _logger.debug(str(m))
                            return (res, (phase_transition, (src_phase, m.as_diagram(i=0))))
                        elif utils.args.use_z3_unsat_cores:
                            assert core is not None
                            uc = solver.unsat_core()
                            # if _logger.isEnabledFor(logging.DEBUG):
                            #     _logger.debug('uc')
                            #     _logger.debug(str(sorted(uc, key=lambda y: y.decl().name())))

                                # _logger.debug('assertions')
                                # _logger.debug(str(solver.assertions()))

                            res = solver.check([diag.trackers[i] for i in core])
                            if res == z3.unsat:
                                _logger.debug('but existing core sufficient, skipping')
                                continue

                            for x in sorted(uc, key=lambda y: y.decl().name()):
                                assert isinstance(x, z3.ExprRef)
                                core.add(int(x.decl().name()[1:]))
                            if _logger.isEnabledFor(logging.DEBUG):
                                _logger.debug('new core')
                                _logger.debug(str(sorted(core)))

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
        for src, transitions in self.automaton.transitions_to_grouped_by_src(current_phase).items():
            _logger.debug("check transition from %s by %s" % (src.name(), str(list(transitions))))

            ans = check_two_state_implication_along_transitions(solver, self.prog, # TODO: OK to use clean solver here?
                                                                pre_frame.summary_of(src), transitions,
                                                                c)
            if ans is not None:
                return (src, ans)

        return None


    def _simplify_summary(self, f: MySet[Expr], p: Phase) -> None:
        l = []
        for c in reversed(f.l):
            f_minus_c = [x for x in f.l if x in f.s and x is not c]
            if c not in phase_safety(p) and \
               check_implication(self.solver, f_minus_c, [c]) is None:
                _logger.debug('removed %s' % c)
                f.s.remove(c)
            else:
                l.append(c)
        l.reverse()
        f.l = l


    @utils.log_start_end_xml(_logger)
    def simplify(self) -> None:
        for i, f in enumerate(self.fs):
            for p in self.automaton.phases():
                with utils.LogTag(_logger, 'simplify', frame=str(i)):
                    _logger.debug('simplifying frame %d, pred %s' % (i, p.name()))
                    self._simplify_summary(f.summary_of(p), p)


    def print_frame(self, i: int, lvl: int=logging.INFO) -> None:
        f = self.fs[i]
        with utils.LogTag(_logger, 'frame', i=str(i)):
            for p in self.automaton.phases():
                _logger.log_list(lvl, ['frame %d of %s is' % (i, p.name())] + [str(x) for x in f.summary_of(p)])

    def print_frames(self, lvl: int=logging.INFO) -> None:
        for i, _ in enumerate(self.fs):
            self.print_frame(i, lvl=lvl)

    def search(self) -> Frame:
        while True:
            n = len(self) - 1
            with utils.LogTag(_logger, 'frame', lvl=logging.INFO, n=str(n)):
                with utils.LogTag(_logger, 'current-frames', lvl=logging.INFO):
                    self.print_frames()

                _logger.info('considering frame %s' % (len(self) - 1,))

                f = self.get_inductive_frame()
                if f is not None:
                    _logger.always_print('frame is safe and inductive. done!')
                    for p in self.automaton.phases():
                        _logger.log_list(utils.MyLogger.ALWAYS_PRINT, ['summary of %s: ' % p.name()] + [str(x) for x in f.summary_of(p)])
                    return f

                _logger.info('frame is safe but not inductive. starting new frame')
                self.new_frame()

def get_safety(prog: Program) -> List[Expr]:
    if utils.args.safety is not None:
        the_inv: Optional[InvariantDecl] = None
        for inv in prog.invs():
            if inv.name == utils.args.safety:
                the_inv = inv
        if the_inv is None:
            raise Exception('No safety invariant named %s' % utils.args.safety)
        safety: List[Expr] = [the_inv.expr]
    else:
        safety = [s.expr for s in prog.safeties()]

    return safety


@utils.log_start_end_xml(_logger, logging.INFO)
@utils.log_start_end_time(_logger, logging.INFO)
def updr(s: Solver, prog: Program) -> None:
    if utils.args.use_z3_unsat_cores:
        z3.set_param('smt.core.minimize', True)

    check_init(s, prog, safety_only=True)

    fs = Frames(s, prog)
    fs.search()

def debug_tokens(filename: str) -> None:
    l = parser.get_lexer()

    with open(filename) as f:
        l.input(f.read())

    while True:
        tok = l.token()
        if not tok:
            break      # No more input
        _logger.always_print(str(tok))


def check_automaton_init(s: Solver, prog: Program, a: AutomatonDecl) -> None:
    _logger.always_print('checking automaton init:')

    t = s.get_translator(KEY_ONE)

    init_decl = a.the_init()
    assert init_decl is not None  # checked by resolver
    init_phase = prog.scope.get_phase(init_decl.phase)
    assert init_phase is not None  # checked by resolver

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
                _logger.always_print('  implies phase invariant%s... ' % msg, end='')
                sys.stdout.flush()

                check_unsat([(inv.tok, 'phase invariant%s may not hold in initial state' % msg)], s, prog, [KEY_ONE])

def check_automaton_edge_covering(s: Solver, prog: Program, a: AutomatonDecl) -> None:
    _logger.always_print('checking automaton edge covering:')

    t = s.get_translator(KEY_NEW, KEY_OLD)

    for phase in a.phases():
        _logger.always_print('  checking phase %s:' % phase.name)
        with s:
            for inv in phase.invs():
                s.add(t.translate_expr(inv.expr, old=True))

            for trans in prog.transitions():
                if any(delta.transition == trans.name and delta.precond is None for delta in phase.transitions()):
                    _logger.always_print('    transition %s is covered trivially.' % trans.name)
                    continue

                _logger.always_print('    checking transition %s is covered... ' % trans.name, end='')

                with s:
                    s.add(t.translate_transition(trans))
                    s.add(z3.And(*(z3.Not(t.translate_precond_of_transition(delta.precond, trans))
                                   for delta in phase.transitions() if trans.name == delta.transition)))

                    check_unsat([(phase.tok, 'transition %s is not covered by this phase' %
                                  (trans.name, )),
                                 (trans.tok, 'this transition misses transitions from phase %s' % (phase.name,))],
                                s, prog, [KEY_OLD, KEY_NEW])


def check_automaton_inductiveness(s: Solver, prog: Program, a: AutomatonDecl) -> None:
    _logger.always_print('checking automaton inductiveness:')

    t = s.get_translator(KEY_NEW, KEY_OLD)

    for phase in a.phases():
        _logger.always_print('  checking phase %s:' % phase.name)

        with s:
            for inv in phase.invs():
                s.add(t.translate_expr(inv.expr, old=True))

            for delta in phase.transitions():
                trans = prog.scope.get_definition(delta.transition)
                assert trans is not None
                precond = delta.precond
                target = prog.scope.get_phase(delta.target) if delta.target is not None else phase
                assert target is not None

                trans_pretty = '(%s, %s)' % (trans.name, str(precond) if (precond is not None) else 'true')
                _logger.always_print('    checking transition: %s' % trans_pretty)

                with s:
                    s.add(t.translate_transition(trans, precond=precond))
                    for inv in target.invs():
                        with s:
                            s.add(z3.Not(t.translate_expr(inv.expr)))

                            if inv.tok is not None:
                                msg = ' on line %d' % inv.tok.lineno
                            else:
                                msg = ''
                            _logger.always_print('      preserves invariant%s... ' % msg, end='')
                            sys.stdout.flush()

                            check_unsat([(inv.tok, 'invariant%s may not be preserved by transition %s in phase %s' %
                                          (msg, trans_pretty, phase.name)),
                                         (delta.tok, 'this transition may not preserve invariant%s' % (msg,))],
                                        s, prog, [KEY_OLD, KEY_NEW])

@utils.log_start_end_time(_logger, logging.INFO)
def verify(s: Solver, prog: Program) -> None:
    old_count = utils.error_count
    a = prog.the_automaton()
    if a is None:
        if utils.args.automaton == 'only':
            utils.print_error_and_exit(None, "--automaton='only' requires the file to declare an automaton")
    elif utils.args.automaton != 'no':
        check_automaton_full(s, prog, a)

    if utils.args.automaton != 'only':
        check_init(s, prog)
        check_transitions(s, prog)

    if utils.error_count == old_count:
        _logger.always_print('all ok!')
    else:
        _logger.always_print('program has errors.')

def check_automaton_full(s: Solver, prog: Program, a: AutomatonDecl) -> None:
    check_automaton_init(s, prog, a)
    check_automaton_inductiveness(s, prog, a)
    check_automaton_edge_covering(s, prog, a)

def get_transition_indicator(uid: str, name: str) -> str:
    return '%s_%s_%s' % (TRANSITION_INDICATOR, uid, name)

def assert_any_transition(s: Solver, prog: Program, uid: str, key: str, key_old: str, allow_stutter: bool=False) -> None:
    t = s.get_translator(key, key_old)

    l = []
    for transition in prog.transitions():
        tid = z3.Bool(get_transition_indicator(uid, transition.name))
        l.append(tid)
        s.add(tid == t.translate_transition(transition))

    if allow_stutter:
        tid = z3.Bool(get_transition_indicator(uid, 'stutter'))
        l.append(tid)
        s.add(tid == z3.And(*t.frame([])))

    s.add(z3.Or(*l))

def check_bmc(s: Solver, prog: Program, safety: Expr, depth: int) -> None:
    keys = ['state%2d' % i for i in range(depth+1)]

    if _logger.isEnabledFor(logging.DEBUG):
        _logger.debug('check_bmc property: %s' % safety)
        _logger.debug('check_bmc depth: %s' % depth)

    for k in keys:
        s.get_translator(k)  # initialize all the keys before pushing a solver stack frame

    with s:
        t = s.get_translator(keys[0])
        for init in prog.inits():
            s.add(t.translate_expr(init.expr))

        t = s.get_translator(keys[-1])
        s.add(t.translate_expr(syntax.Not(safety)))

        for i in range(depth):
            assert_any_transition(s, prog, str(i), keys[i+1], keys[i], allow_stutter=True)

        # if _logger.isEnabledFor(logging.DEBUG):
        #     _logger.debug('assertions')
        #     _logger.debug(str(s.assertions()))

        check_unsat([(None, 'found concrete trace violating safety')],
                    s, prog, keys)

@utils.log_start_end_time(_logger)
def bmc(s: Solver, prog: Program) -> None:
    safety = syntax.And(*get_safety(prog))

    n = utils.args.depth

    _logger.always_print('bmc checking the following property to depth %d' % n)
    _logger.always_print('  ' + str(safety))

    start = datetime.now()

    check_bmc(s, prog, safety, n)


@utils.log_start_end_time(_logger)
def theorem(s: Solver, prog: Program) -> None:
    _logger.always_print('checking theorems:')

    for th in prog.theorems():
        if th.twostate:
            keys = [KEY_OLD, KEY_NEW]
        else:
            keys = [KEY_ONE]

        t = s.get_translator(*keys)

        if th.name is not None:
            msg = ' ' + th.name
        elif th.tok is not None:
            msg = ' on line %d' % th.tok.lineno
        else:
            msg = ''

        _logger.always_print(' theorem%s... ' % msg, end='')
        sys.stdout.flush()

        with s:
            s.add(z3.Not(t.translate_expr(th.expr)))

            check_unsat([(th.tok, 'theorem%s may not hold' % msg)], s, prog, keys)

def nop(s: Solver, prog: Program) -> None:
    pass

def ipython(s:Solver, prog: Program) -> None:
    import IPython  # type: ignore
    #IPython.embed()
    IPython.start_ipython(argv=[],user_ns=dict(locals()))

def translate_transition_call(s: Solver, prog: Program, key: str, key_old: str, c: syntax.TransitionCall) -> z3.ExprRef:
    ition = prog.scope.get_definition(c.target)
    assert ition is not None
    lator = s.get_translator(key, key_old)
    bs = lator.bind(ition.binder)
    qs: List[Optional[z3.ExprRef]] = [b for b in bs]
    if c.args is not None:
        for j, a in enumerate(c.args):
            if isinstance(a, Expr):
                bs[j] = lator.translate_expr(a)
                qs[j] = None
            else:
                assert isinstance(a, syntax.Star)
                pass
    qs1 = [q for q in qs if q is not None]
    with lator.scope.in_scope(ition.binder, bs):
        body = lator.translate_transition_body(ition)
    if len(qs1) > 0:
        return z3.Exists(qs1, body)
    else:
        return body

def trace(s: Solver, prog: Program) -> None:
    if len(list(prog.traces())) > 0:
        _logger.always_print('finding traces:')

    for trace in prog.traces():
        n_states = len(list(trace.transitions())) + 1
        print('%s states' % (n_states,))

        keys = ['state%2d' % i for i in range(n_states)]

        for k in keys:
            s.get_translator(k)  # initialize all the keys before pushing a solver stack frame

        with s:
            lator = s.get_translator(keys[0])
            if len(trace.components) > 0 and not isinstance(trace.components[0], syntax.AssertDecl):
                for init in prog.inits():
                    s.add(lator.translate_expr(init.expr))

            i = 0
            for c in trace.components:
                if isinstance(c, syntax.AssertDecl):
                    if c.expr is None:
                        if i != 0:
                            utils.print_error_and_exit(c.tok, 'assert init is only allowed in the first state')
                        for init in prog.inits():
                            s.add(s.get_translator(keys[i]).translate_expr(init.expr))
                    else:
                        s.add(s.get_translator(keys[i]).translate_expr(c.expr))
                else:
                    te: syntax.TransitionExpr = c.transition
                    if isinstance(te, syntax.AnyTransition):
                        assert_any_transition(s, prog, str(i), keys[i+1], keys[i], allow_stutter=True)
                    else:
                        l = []
                        for call in te.calls:
                            tid = z3.Bool(get_transition_indicator(str(i), call.target))
                            l.append(tid)
                            s.add(tid == translate_transition_call(s, prog, keys[i+1], keys[i], call))
                        s.add(z3.Or(*l))

                    i += 1

            res = check_unsat([], s, prog, keys)
            if (res == z3.sat) != trace.sat:
                utils.print_error(trace.tok, 'trace declared %s but was %s!' % ('sat' if trace.sat else 'unsat', res))


def parse_args() -> argparse.Namespace:
    argparser = argparse.ArgumentParser()

    subparsers = argparser.add_subparsers(title='subcommands')
    all_subparsers = []

    verify_subparser = subparsers.add_parser('verify', help='verify that the invariants are inductive')
    verify_subparser.set_defaults(main=verify)
    all_subparsers.append(verify_subparser)

    updr_subparser = subparsers.add_parser('updr', help='search for a strengthening that proves the invariant named by the --safety=NAME flag')
    updr_subparser.set_defaults(main=updr)
    all_subparsers.append(updr_subparser)

    bmc_subparser = subparsers.add_parser('bmc', help='bounded model check to depth given by the --depth=DEPTH flag for property given by the --safety=NAME flag')
    bmc_subparser.set_defaults(main=bmc)
    all_subparsers.append(bmc_subparser)

    theorem_subparser = subparsers.add_parser('theorem', help='check state-independent theorems about the background axioms of a model')
    theorem_subparser.set_defaults(main=theorem)
    all_subparsers.append(theorem_subparser)

    trace_subparser = subparsers.add_parser('trace', help='search for concrete executions that satisfy query described by the file\'s trace declaration')
    trace_subparser.set_defaults(main=trace)
    all_subparsers.append(trace_subparser)

    generate_parser_subparser = subparsers.add_parser('generate-parser', help='internal command used by benchmarking infrastructure to avoid certain race conditions')
    generate_parser_subparser.set_defaults(main=nop)  # parser is generated implicitly by main when it parses the program
    all_subparsers.append(generate_parser_subparser)

    typecheck_subparser = subparsers.add_parser('typecheck', help='typecheck the file, report any errors, and exit')
    typecheck_subparser.set_defaults(main=nop)  # program is always typechecked; no further action required
    all_subparsers.append(typecheck_subparser)

    ipython_subparser = subparsers.add_parser('ipython', help='start IPython shell with s and prog')
    ipython_subparser.set_defaults(main=ipython)
    all_subparsers.append(ipython_subparser)

    all_subparsers += pd.pd_add_argparsers(subparsers)

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
        s.add_argument('--timeout', type=int, default=None,
                       help='z3 timeout (milliseconds)')
        s.add_argument('--exit-on-error', action='store_true',
                       help='exit after reporting first error')


    updr_subparser.add_argument('--dont-use-z3-unsat-cores', action='store_false', dest='use_z3_unsat_cores',
                                help='generalize diagrams using brute force instead of unsat cores')
    updr_subparser.add_argument('--smoke-test', action='store_true',
                                help='(for debugging mypyvy itself) run bmc to confirm every conjunct added to a frame')
    updr_subparser.add_argument('--assert-inductive-trace', action='store_true',
                                help='(for debugging mypyvy itself) check that frames are always inductive')

    updr_subparser.add_argument('--sketch', action='store_true',
                                help='use sketched invariants as additional safety (currently only in automaton)')

    updr_subparser.add_argument('--simple-conjuncts', action='store_true',
                                help='substitute existentially quantified variables that are equal to constants')
    updr_subparser.add_argument('--dont-simplify-diagram', action='store_false', dest='simplify_diagram',
                                help='in diagram generation, refrain from substituting existentially quantified variables that are equal to constants')
    updr_subparser.add_argument('--automaton', action='store_true',
                                help='whether to run vanilla UPDR or phase UPDR')
    updr_subparser.add_argument('--block-may-cexs', action='store_true',
                                help="treat failures to push as additional proof obligations")
    updr_subparser.add_argument('--push-frame-zero', default='if_trivial', choices=['if_trivial', 'always', 'never'],
                                help="push lemmas from the initial frame: always/never/if_trivial, the latter is when there is more than one phase")

    verify_subparser.add_argument('--automaton', default='yes', choices=['yes', 'no', 'only'],
                                  help="whether to use phase automata during verification. by default ('yes'), both non-automaton "
                                  "and automaton proofs are checked. 'no' means ignore automaton proofs. "
                                  "'only' means ignore non-automaton proofs.")
    verify_subparser.add_argument('--check-transition', default=None, nargs='+',
                                  help="when verifying inductiveness, check only these transitions")
    verify_subparser.add_argument('--check-invariant', default=None, nargs='+',
                                  help="when verifying inductiveness, check only these invariants")

    bmc_subparser.add_argument('--safety', help='property to check')
    bmc_subparser.add_argument('--depth', type=int, default=3, metavar='N',
                               help='number of steps to check')

    argparser.add_argument('filename')

    return argparser.parse_args()

class MyFormatter(logging.Formatter):
    def __init__(self, fmt: str) -> None:
        super().__init__(fmt='%(levelname)s ' + fmt)
        self.withoutlevel = logging.Formatter(fmt='%(message)s')
        self.start = datetime.now()

    def format(self, record: Any) -> str:
        if record.levelno == utils.MyLogger.ALWAYS_PRINT:
            return self.withoutlevel.format(record)
        else:
            return super().format(record)

    def formatTime(self, record: Any, datefmt: Optional[str]=None) -> str:
        return str((datetime.now() - self.start).total_seconds())

def main() -> None:
    utils.args = parse_args()

    if utils.args.log_xml:
        fmt = '%(message)s'
    elif utils.args.log_time:
        fmt = '%(asctime)s %(filename)s:%(lineno)d: %(message)s'
    else:
        fmt = '%(filename)s:%(lineno)d: %(message)s'

    _logger.setLevel(getattr(logging, utils.args.log.upper(), None))
    handler = logging.StreamHandler(stream=sys.stdout)
    handler.terminator = ''
    handler.setFormatter(MyFormatter(fmt))
    logging.root.addHandler(handler)
    # _logger.addHandler(handler)

    if utils.args.key_prefix is not None:
        global KEY_ONE
        global KEY_NEW
        global KEY_OLD

        KEY_ONE = utils.args.key_prefix + '_' + KEY_ONE
        KEY_NEW = utils.args.key_prefix + '_' + KEY_NEW
        KEY_OLD = utils.args.key_prefix + '_' + KEY_OLD

    with utils.LogTag(_logger, 'main', lvl=logging.INFO):
        _logger.always_print(' '.join(['python3.7'] + sys.argv))


        _logger.info('setting seed to %d' % utils.args.seed)
        z3.set_param('smt.random_seed', utils.args.seed)

        # _logger.info('enable z3 macro finder')
        # z3.set_param('smt.macro_finder', True)

        if utils.args.timeout is not None:
            _logger.info('setting z3 timeout to %s' % utils.args.timeout)
            z3.set_param('timeout', utils.args.timeout)

        pre_parse_error_count = utils.error_count

        with open(utils.args.filename) as f:
            l = parser.get_lexer()
            p = parser.get_parser(forbid_rebuild=utils.args.forbid_parser_rebuild)
            prog: syntax.Program = p.parse(input=f.read(), lexer=l, filename=utils.args.filename)

        if utils.args.print_program_repr:
            _logger.always_print(repr(prog))
        if utils.args.print_program:
            _logger.always_print(str(prog))

        if utils.error_count > pre_parse_error_count:
            _logger.always_print('program has syntax errors.')
            sys.exit(1)

        pre_resolve_error_count = utils.error_count

        prog.resolve()
        if utils.error_count > pre_resolve_error_count:
            _logger.always_print('program has resolution errors.')
            sys.exit(1)

        scope = prog.scope
        assert scope is not None
        assert len(scope.stack) == 0

        s = Solver(cast(Scope[z3.ExprRef], scope))
        t = s.get_translator()
        for a in prog.axioms():
            s.add(t.translate_expr(a.expr))

        s.register_mutable_axioms(r.derived_axiom for r in prog.derived_relations() if r.derived_axiom is not None)

        utils.args.main(s, prog)

        _logger.info('total number of queries: %s' % s.nqueries)

    sys.exit(1 if utils.error_count > 0 else 0)


if __name__ == '__main__':
    main()