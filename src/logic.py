from __future__ import annotations
from collections import OrderedDict, defaultdict
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime
import time
import itertools
import io
import logging
import re
import sys
from typing import List, Any, Optional, Set, Tuple, Union, Iterable, Dict, Sequence, Iterator, \
    cast, TypeVar
import z3

import utils
from phases import Phase, Frame, PhaseTransition
import syntax
from syntax import Expr, Scope, ConstantDecl, RelationDecl, SortDecl, \
    FunctionDecl, DefinitionDecl

z3.Forall = z3.ForAll

KEY_ONE = 'one'
KEY_NEW = 'new'
KEY_OLD = 'old'
TRANSITION_INDICATOR = 'tid'

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

def check_unsat(
        errmsgs: List[Tuple[Optional[syntax.Token], str]],
        s: Solver,
        keys: List[str]
) -> Optional[Trace]:
    start = datetime.now()
    # if logger.isEnabledFor(logging.DEBUG):
    #     logger.debug('assertions')
    #     logger.debug(str(s.assertions()))

    res = s.check()
    if res != z3.unsat:
        if res == z3.sat:
            m = Trace.from_z3(keys, s.model())

            utils.logger.always_print('')
            if utils.args.print_counterexample:
                utils.logger.always_print(str(m))
        else:
            assert res == z3.unknown
            utils.logger.always_print('unknown!')
            utils.logger.always_print('reason unknown: ' + s.reason_unknown())
            assert False, 'unexpected unknown from z3!'
        for tok, msg in errmsgs:
            utils.print_error(tok, msg)

        return m
    else:
        if not utils.args.query_time:
            time_msg = ''
        else:
            time_msg = ' (%s)' % (datetime.now() - start, )
        utils.logger.always_print('ok.%s' % (time_msg,))

        sys.stdout.flush()
        return None


@utils.log_start_end_xml(utils.logger, logging.INFO)
def check_init(s: Solver, safety_only: bool = False) -> Optional[Tuple[syntax.InvariantDecl, Trace]]:
    utils.logger.always_print('checking init:')

    prog = syntax.the_program
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
                utils.logger.always_print('  implies invariant%s... ' % msg, end='')
                sys.stdout.flush()

                res = check_unsat([(inv.tok, 'invariant%s may not hold in initial state' % msg)],
                                  s, [KEY_ONE])
                if res is not None:
                    return inv, res
    return None

def check_transitions(s: Solver) -> Optional[Tuple[syntax.InvariantDecl, Trace, DefinitionDecl]]:
    t = s.get_translator(KEY_NEW, KEY_OLD)
    prog = syntax.the_program

    with s:
        for inv in prog.invs():
            s.add(t.translate_expr(inv.expr, old=True))

        for trans in prog.transitions():
            if utils.args.check_transition is not None and \
               trans.name not in utils.args.check_transition:
                continue

            utils.logger.always_print('checking transation %s:' % (trans.name,))

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
                        utils.logger.always_print('  preserves invariant%s... ' % msg, end='')
                        sys.stdout.flush()

                        res = check_unsat([(inv.tok, 'invariant%s may not be preserved by transition %s'
                                            % (msg, trans.name)),
                                           (trans.tok, 'this transition may not preserve invariant%s'
                                            % (msg,))],
                                          s, [KEY_OLD, KEY_NEW])
                        if res is not None:
                            return inv, res, trans
    return None

def check_implication(
        s: Solver,
        hyps: Iterable[Expr],
        concs: Iterable[Expr],
        minimize: Optional[bool] = None
) -> Optional[z3.ModelRef]:
    t = s.get_translator(KEY_ONE)
    with s:
        for e in hyps:
            s.add(t.translate_expr(e))
        for e in concs:
            with s:
                s.add(z3.Not(t.translate_expr(e)))
                # if utils.logger.isEnabledFor(logging.DEBUG):
                #     utils.logger.debug('assertions')
                #     utils.logger.debug(str(s.assertions()))

                if s.check() != z3.unsat:
                    return s.model(minimize=minimize)

    return None

def check_two_state_implication_all_transitions(
        s: Solver,
        old_hyps: Iterable[Expr],
        new_conc: Expr,
        minimize: Optional[bool] = None,
) -> Optional[Tuple[z3.ModelRef, DefinitionDecl]]:
    t = s.get_translator(KEY_NEW, KEY_OLD)
    prog = syntax.the_program
    with s:
        for h in old_hyps:
            s.add(t.translate_expr(h, old=True))

        s.add(z3.Not(t.translate_expr(new_conc)))

        for trans in prog.transitions():
            with s:
                s.add(t.translate_transition(trans))

                # if utils.logger.isEnabledFor(logging.DEBUG):
                #     utils.logger.debug('assertions')
                #     utils.logger.debug(str(s.assertions()))
                print(f'check_two_state_implication_all_transitions: checking {trans.name}... ', end='')
                res = s.check()
                assert res in (z3.sat, z3.unsat), res
                print(res)
                if res != z3.unsat:
                    return s.model(minimize=minimize), trans

    return None


def get_transition_indicator(uid: str, name: str) -> str:
    return '%s_%s_%s' % (TRANSITION_INDICATOR, uid, name)

def assert_any_transition(s: Solver, uid: str,
                          key: str, key_old: str, allow_stutter: bool = False) -> None:
    t = s.get_translator(key, key_old)
    prog = syntax.the_program

    tids = []
    for transition in prog.transitions():
        tid = z3.Bool(get_transition_indicator(uid, transition.name))
        tids.append(tid)
        s.add(z3.Implies(tid, t.translate_transition(transition)))

    if allow_stutter:
        tid = z3.Bool(get_transition_indicator(uid, '$stutter'))
        tids.append(tid)
        s.add(z3.Implies(tid, z3.And(*t.frame([]))))

    s.add(z3.Or(*tids))

def check_bmc(s: Solver, safety: Expr, depth: int, preconds: Optional[Iterable[Expr]] = None) -> Optional[Trace]:
    keys = ['state%02d' % i for i in range(depth + 1)]
    prog = syntax.the_program

    if preconds is None:
        preconds = (init.expr for init in prog.inits())

    if utils.logger.isEnabledFor(logging.DEBUG):
        utils.logger.debug('check_bmc property: %s' % safety)
        utils.logger.debug('check_bmc depth: %s' % depth)

    for k in keys:
        s.get_translator(k)  # initialize all the keys before pushing a solver stack frame

    with s:
        t = s.get_translator(keys[0])
        for precond in preconds:
            s.add(t.translate_expr(precond))

        t = s.get_translator(keys[-1])
        s.add(t.translate_expr(syntax.Not(safety)))

        for i in range(depth):
            if i != len(keys) - 1:
                t = s.get_translator(keys[i])
                s.add(t.translate_expr(safety))
            assert_any_transition(s, str(i), keys[i + 1], keys[i], allow_stutter=False)

        res = s.check()
        if res == z3.sat:
            m = Trace.from_z3(list(reversed(keys)), s.model())
            return m
        elif res == z3.unknown:
            print('unknown!')
        return None


def check_two_state_implication_along_transitions(
        s: Solver,
        old_hyps: Iterable[Expr],
        transitions: Sequence[PhaseTransition],
        new_conc: Expr,
        minimize: Optional[bool] = None
) -> Optional[Tuple[z3.ModelRef, PhaseTransition]]:
    t = s.get_translator(KEY_NEW, KEY_OLD)
    prog = syntax.the_program
    with s:
        for h in old_hyps:
            s.add(t.translate_expr(h, old=True))

        s.add(z3.Not(t.translate_expr(new_conc)))

        for phase_transition in transitions:
            delta = phase_transition.transition_decl()
            trans = prog.scope.get_definition(delta.transition)
            assert trans is not None
            precond = delta.precond

            with s:
                s.add(t.translate_transition(trans, precond=precond))
                if s.check() != z3.unsat:
                    return s.model(minimize=minimize), phase_transition

    return None


class Solver(object):
    def __init__(self, include_program: bool = True) -> None:
        self.z3solver = z3.Solver()
        prog = syntax.the_program
        assert prog.scope is not None
        assert len(prog.scope.stack) == 0
        self.scope = cast(Scope[z3.ExprRef], prog.scope)
        self.translators: Dict[Tuple[Optional[str], Optional[str]], syntax.Z3Translator] = {}
        self.nqueries = 0
        self.assumptions_necessary = False
        self.known_keys: Set[str] = set()
        self.mutable_axioms: List[Expr] = []
        self.stack: List[List[z3.ExprRef]] = [[]]
        self.include_program = include_program

        if include_program:
            self.register_mutable_axioms(r.derived_axiom for r in prog.derived_relations()
                                         if r.derived_axiom is not None)
            t = self.get_translator()
            for a in prog.axioms():
                self.add(t.translate_expr(a.expr))

    def restart(self) -> None:
        print('z3solver restart!')
        self.z3solver = z3.Solver()
        for i, frame in enumerate(self.stack):
            if i > 0:
                self.z3solver.push()
            for e in frame:
                self.z3solver.add(e)

    def register_mutable_axioms(self, axioms: Iterable[Expr]) -> None:
        assert self.include_program
        assert len(self.known_keys) == 0, \
            "mutable axioms must be registered before any keys are known to the solver!"
        self.mutable_axioms.extend(axioms)

    def _initialize_key(self, key: Optional[str]) -> None:
        assert self.include_program
        if key is not None and key not in self.known_keys:
            self.known_keys.add(key)

            assert self.z3solver.num_scopes() == 0, \
                "the first time get_translator is called with a particular key, " + \
                "there must be no scopes pushed on the Z3 stack!"

            t = self.get_translator(key)
            for a in self.mutable_axioms:
                self.add(t.translate_expr(a))

    def get_translator(self, key: Optional[str] = None, key_old: Optional[str] = None) \
            -> syntax.Z3Translator:
        assert self.include_program
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

    def push(self) -> None:
        self.stack.append([])
        self.z3solver.push()

    def pop(self) -> None:
        self.stack.pop()
        self.z3solver.pop()

    def __enter__(self) -> None:
        self.push()

    def __exit__(self, exn_type: Any, exn_value: Any, traceback: Any) -> None:
        self.pop()

    def add(self, e: z3.ExprRef) -> None:
        # if logger.isEnabledFor(logging.DEBUG):
        #     logger.debug('adding %s' % e)

        self.stack[-1].append(e)
        self.z3solver.add(e)

    def check(self, assumptions: Optional[Sequence[z3.ExprRef]] = None) -> z3.CheckSatResult:
        # logger.debug('solver.check')
        if assumptions is None:
            assert not self.assumptions_necessary
            assumptions = []
        self.nqueries += 1

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
                for e in self.assertions():
                    print(e)
                print('stats:')
                print(self.z3solver.statistics())
                print(self.z3solver.to_smt2())

                print('trying fresh solver')
                s2 = z3.Solver()
                lator = self.get_translator()
                for a in syntax.the_program.axioms():
                    s2.add(lator.translate_expr(a.expr))
                for e in self.assertions():
                    s2.add(e)

                print('s2.check()', s2.check())
                print('s2 stats:')
                print(s2.statistics())
                print(s2.to_smt2())

                print('trying fresh context')
                ctx = z3.Context()
                s3 = z3.Solver(ctx=ctx)
                for a in syntax.the_program.axioms():
                    s3.add(lator.translate_expr(a.expr).translate(ctx))
                for e in self.assertions():
                    s3.add(e.translate(ctx))

                print('s3.check()', s3.check())
                print('s3 stats:')
                print(s3.statistics())
                print(s3.to_smt2())

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
            print(f'z3solver returned {ans} after {1000*(time.time() - t_start):.1f}ms (timeout was {tmt}ms), trying again')
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
        if minimize is None:
            minimize = utils.args.minimize_models
        if minimize:
            if sorts_to_minimize is None:
                sorts_to_minimize = [s.to_z3() for s in self.scope.sorts.values() if not syntax.has_annotation(s, 'no_minimize')]
            if relations_to_minimize is None:
                m = self.z3solver.model()
                ds = m.decls()
                rels_to_minimize = []
                for r in self.scope.relations.values():
                    if r.is_derived() or syntax.has_annotation(r, 'no_minimize'):
                        continue
                    if not r.mutable:
                        z3r = r.to_z3(None)
                        if isinstance(z3r, z3.ExprRef):
                            rels_to_minimize.append(z3r.decl())
                        else:
                            rels_to_minimize.append(z3r)
                    else:
                        for k in self.known_keys:
                            z3r = r.to_z3(k)
                            if isinstance(z3r, z3.ExprRef):
                                z3r = z3r.decl()
                            if z3r in ds:
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

        return z3.Forall(x, z3.Or(*disjs))

    def _relational_cardinality_constraint(self, relation: z3.FuncDeclRef, n: int) -> z3.ExprRef:
        if relation.arity() == 0:
            return z3.BoolVal(True)

        consts = [[z3.Const(f'card$_{relation}_{i}_{j}', relation.domain(j))
                   for j in range(relation.arity())]
                  for i in range(n)]

        vs = [z3.Const(f'x$_{relation}_{j}', relation.domain(j)) for j in range(relation.arity())]

        result = z3.Forall(vs, z3.Implies(relation(*vs), z3.Or(*(
            z3.And(*(
                c == v for c, v in zip(cs, vs)
            ))
            for cs in consts
        ))))
        return result

    @utils.log_start_end_xml(utils.logger)
    @utils.log_start_end_time(utils.logger)
    def _minimal_model(
            self,
            assumptions: Optional[Sequence[z3.ExprRef]],
            sorts_to_minimize: Iterable[z3.SortRef],
            relations_to_minimize: Iterable[z3.FuncDeclRef],
    ) -> z3.ModelRef:
        with self:
            for x in itertools.chain(
                    cast(Iterable[Union[z3.SortRef, z3.FuncDeclRef]], sorts_to_minimize),
                    relations_to_minimize):
                with utils.LogTag(utils.logger, 'sort-or-rel', obj=str(x)):
                    for n in itertools.count(1):
                        with utils.LogTag(utils.logger, 'card', n=str(n)):
                            with self:
                                self.add(self._cardinality_constraint(x, n))
                                res = self.check(assumptions)
                                if res == z3.sat:
                                    break
                    with utils.LogTag(utils.logger, 'answer', obj=str(x), n=str(n)):
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
        self.tombstones: Dict[_RelevantDecl, Optional[Set[int]]] = defaultdict(set)

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
            self.reverse_map: List[Tuple[_RelevantDecl, int]] = []
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
        vs = self.binder.vs

        return syntax.Exists(vs, e)

    # TODO: can be removed? replaced with Frames.valid_in_initial_frame (YF)
    def valid_in_init(self, s: Solver, minimize: Optional[bool] = None) -> bool:
        prog = syntax.the_program
        return check_implication(s, (init.expr for init in prog.inits()),
                                 [syntax.Not(self.to_ast())], minimize=minimize) is None

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
        self.binder.vs = [v for v in self.binder.vs
                          if any(v.name in c.free_ids() for _, _, c in self.conjuncts())]

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

    def smoke(self, s: Solver, depth: Optional[int]) -> None:
        if utils.args.smoke_test and depth is not None:
            utils.logger.debug('smoke testing at depth %s...' % (depth,))
            utils.logger.debug(str(self))
            check_bmc(s, syntax.Not(self.to_ast()), depth)

    # TODO: merge similarities with clause_implied_by_transitions_from_frame...
    def check_valid_in_phase_from_frame(
            self, s: Solver, f: Frame,
            transitions_to_grouped_by_src: Dict[Phase, Sequence[PhaseTransition]],
            propagate_init: bool,
            minimize: Optional[bool] = None
    ) -> bool:
        for src, transitions in transitions_to_grouped_by_src.items():
            ans = check_two_state_implication_along_transitions(
                s, f.summary_of(src), transitions, syntax.Not(self.to_ast()),
                minimize=minimize)
            if ans is not None:
                return False

        if propagate_init:
            return self.valid_in_init(s, minimize=minimize)
        return True

    @utils.log_start_end_xml(utils.logger)
    @utils.log_start_end_time(utils.logger)
    def generalize(self, s: Solver, f: Frame,
                   transitions_to_grouped_by_src: Dict[Phase, Sequence[PhaseTransition]],
                   propagate_init: bool,
                   depth: Optional[int] = None) -> None:
        if utils.logger.isEnabledFor(logging.DEBUG):
            utils.logger.debug('generalizing diagram')
            utils.logger.debug(str(self))
            with utils.LogTag(utils.logger, 'previous-frame', lvl=logging.DEBUG):
                for p in f.phases():
                    utils.logger.log_list(logging.DEBUG, ['previous frame for %s is' % p.name()] +
                                          [str(x) for x in f.summary_of(p)])

        d: _RelevantDecl
        I: Iterable[_RelevantDecl] = self.ineqs
        R: Iterable[_RelevantDecl] = self.rels
        C: Iterable[_RelevantDecl] = self.consts
        F: Iterable[_RelevantDecl] = self.funcs

        self.smoke(s, depth)

        with utils.LogTag(utils.logger, 'eliminating-conjuncts', lvl=logging.DEBUG):
            for d in itertools.chain(I, R, C, F):
                if isinstance(d, SortDecl) and len(self.ineqs[d]) == 1:
                    continue
                with self.without(d):
                    res = self.check_valid_in_phase_from_frame(
                        s, f, transitions_to_grouped_by_src, propagate_init, minimize=False)
                if res:
                    if utils.logger.isEnabledFor(logging.DEBUG):
                        utils.logger.debug('eliminated all conjuncts from declaration %s' % d)
                    self.remove_clause(d)
                    self.smoke(s, depth)
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
                        res = self.check_valid_in_phase_from_frame(
                            s, f, transitions_to_grouped_by_src, propagate_init, minimize=False)
                    if res:
                        if utils.logger.isEnabledFor(logging.DEBUG):
                            utils.logger.debug(f'eliminated all negative conjuncts from decl {d}')
                        self.remove_clause(d, cs)
                        self.smoke(s, depth)

            for d, j, c in self.conjuncts():
                with self.without(d, j):
                    res = self.check_valid_in_phase_from_frame(
                        s, f, transitions_to_grouped_by_src, propagate_init, minimize=False)
                if res:
                    if utils.logger.isEnabledFor(logging.DEBUG):
                        utils.logger.debug('eliminated clause %s' % c)
                    self.remove_clause(d, j)
                    self.smoke(s, depth)

        self.prune_unused_vars()

        if utils.logger.isEnabledFor(logging.DEBUG):
            utils.logger.debug('generalized diag')
            utils.logger.debug(str(self))

_digits_re = re.compile(r'(?P<prefix>.*?)(?P<suffix>[0-9]+)$')

def try_printed_by(state: State, s: SortDecl, elt: str) -> Optional[str]:
    custom_printer_annotation = syntax.get_annotation(s, 'printed_by')

    if custom_printer_annotation is not None:
        assert len(custom_printer_annotation.args) >= 1
        import importlib
        printers = importlib.import_module('printers')
        printer_name = custom_printer_annotation.args[0]
        custom_printer = printers.__dict__.get(printer_name)
        custom_printer_args = custom_printer_annotation.args[1:] \
            if custom_printer is not None else []
        if custom_printer is not None:
            return custom_printer(state, s, elt, custom_printer_args)
        else:
            utils.print_warning(custom_printer_annotation.tok,
                                'could not find printer named %s' % (printer_name,))
    return None

def print_element(state: State, s: Union[SortDecl, syntax.Sort], elt: str) -> str:
    if not isinstance(s, SortDecl):
        s = syntax.get_decl_from_sort(s)

    return try_printed_by(state, s, elt) or elt

def print_tuple(state: State, arity: List[syntax.Sort], tup: List[str]) -> str:
    l = []
    assert len(arity) == len(tup)
    for s, x in zip(arity, tup):
        l.append(print_element(state, s, x))
    return ','.join(l)

def univ_str(state: State) -> List[str]:
    l = []
    for s in sorted(state.univs.keys(), key=str):
        if syntax.has_annotation(s, 'no_print'):
            continue

        l.append(str(s))

        def key(x: str) -> Tuple[str, int]:
            ans = print_element(state, s, x)
            m = _digits_re.match(ans)
            if m is not None:
                return (m['prefix'], int(m['suffix']))
            else:
                return (ans, 0)
        for x in sorted(state.univs[s], key=key):
            l.append('  %s' % print_element(state, s, x))
    return l

def _state_str(
        state: State,
        Cs: Dict[ConstantDecl, str],
        Rs: Dict[RelationDecl, List[Tuple[List[str], bool]]],
        Fs: Dict[FunctionDecl, List[Tuple[List[str], str]]]
) -> str:
    l = []
    for C in Cs:
        if syntax.has_annotation(C, 'no_print'):
            continue
        l.append('%s = %s' % (C.name, print_element(state, C.sort, Cs[C])))

    for R in Rs:
        if syntax.has_annotation(R, 'no_print'):
            continue
        for tup, b in sorted(Rs[R], key=lambda x: print_tuple(state, R.arity, x[0])):
            if b:
                l.append('%s%s(%s)' % ('' if b else '!', R.name,
                                       print_tuple(state, R.arity, tup)))

    for F in Fs:
        if syntax.has_annotation(F, 'no_print'):
            continue
        for tup, res in sorted(Fs[F], key=lambda x: print_tuple(state, F.arity, x[0])):
            l.append('%s(%s) = %s' % (F.name, print_tuple(state, F.arity, tup),
                                      print_element(state, F.sort, res)))

    return '\n'.join(l)


class Trace(object):
    def __init__(
            self,
            keys: List[str],
    ) -> None:
        self.keys = keys

        self.univs: Dict[SortDecl, List[str]] = OrderedDict()

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
        self.onestate_formula_cache: Dict[int, Expr] = {}
        self.diagram_cache: Dict[int, Diagram] = {}

    @staticmethod
    def from_z3(keys: List[str], z3m: z3.ModelRef, allow_undefined: bool = False) -> Trace:
        m = Trace(keys)
        m.read_out(z3m, allow_undefined=allow_undefined)
        return m

    # for pickling
    def __getstate__(self) -> Any:
        return dict(
            self.__dict__,
            z3model=None,
        )
    # __setstate__ is not really needed, since the following is the default:
    # def __setstate__(self, state:Any) -> None:
    #     self.__dict__.update(state)

    def __str__(self) -> str:
        l = []
        dummy_state = State(self.univs, self.immut_rel_interps, self.immut_const_interps,
                            self.immut_func_interps)
        l.extend(univ_str(dummy_state))
        l.append(_state_str(dummy_state, self.immut_const_interps, self.immut_rel_interps,
                            self.immut_func_interps))
        for i, k in enumerate(self.keys):
            if i > 0 and self.transitions[i - 1] != '':
                l.append('\ntransition %s' % (self.transitions[i - 1],))
            l.append('\nstate %s:' % (i,))
            l.append(_state_str(dummy_state, self.const_interps[i], self.rel_interps[i],
                                self.func_interps[i]))

        return '\n'.join(l)

    def read_out(self, z3model: z3.ModelRef, allow_undefined: bool = False) -> None:
        # utils.logger.debug('read_out')
        def rename(s: str) -> str:
            return s.replace('!val!', '')

        def _eval(expr: z3.ExprRef) -> z3.ExprRef:
            ans = z3model.eval(expr, model_completion=True)
            assert bool(ans) is True or bool(ans) is False, (expr, ans)
            return ans

        prog = syntax.the_program

        for z3sort in sorted(z3model.sorts(), key=str):
            sort = prog.scope.get_sort(str(z3sort))
            assert sort is not None
            univ = z3model.get_universe(z3sort)
            self.univs[sort] = list(sorted(rename(str(x)) for x in univ))
            # if utils.logger.isEnabledFor(logging.DEBUG):
            #     utils.logger.debug(str(z3sort))
            #     for x in self.univs[sort]:
            #         utils.logger.debug('  ' + x)

        model_decls = z3model.decls()
        all_decls = model_decls
        for z3decl in sorted(all_decls, key=str):
            z3name = str(z3decl)
            for i, k in enumerate(self.keys):
                if z3name.startswith(k):
                    name = z3name[len(k + '_'):]
                    R = self.rel_interps[i]
                    C = self.const_interps[i]
                    F = self.func_interps[i]
                    break
            else:
                name = z3name
                R = self.immut_rel_interps
                C = self.immut_const_interps
                F = self.immut_func_interps

            decl = prog.scope.get(name)
            assert not isinstance(decl, syntax.Sort) and \
                not isinstance(decl, syntax.SortInferencePlaceholder)
            if decl is not None:
                if isinstance(decl, RelationDecl):
                    if len(decl.arity) > 0:
                        rl = []
                        domains = [z3model.get_universe(z3decl.domain(i))
                                   for i in range(z3decl.arity())]
                        if not any(x is None for x in domains):
                            # Note: if any domain is None, we silently drop this symbol.
                            # It's not entirely clear that this is an ok thing to do.
                            g = itertools.product(*domains)
                            for row in g:
                                relation_expr = z3decl(*row)
                                ans = _eval(relation_expr)
                                rl.append(([rename(str(col)) for col in row], bool(ans)))
                            assert decl not in R
                            R[decl] = rl
                    else:
                        ans = z3model.eval(z3decl())
                        assert decl not in R
                        R[decl] = [([], bool(ans))]
                elif isinstance(decl, FunctionDecl):
                    fl = []
                    domains = [z3model.get_universe(z3decl.domain(i))
                               for i in range(z3decl.arity())]
                    if not any(x is None for x in domains):
                        # Note: if any domain is None, we silently drop this symbol.
                        # It's not entirely clear that this is an ok thing to do.
                        g = itertools.product(*domains)
                        for row in g:
                            ans = z3model.eval(z3decl(*row))
                            fl.append(([rename(str(col)) for col in row],
                                       rename(ans.decl().name())))
                        assert decl not in F
                        F[decl] = fl

                else:
                    assert isinstance(decl, ConstantDecl)
                    v = z3model.eval(z3decl()).decl().name()
                    assert decl not in C
                    C[decl] = rename(v)
            else:
                if name.startswith(TRANSITION_INDICATOR + '_') and z3model.eval(z3decl()):
                    name = name[len(TRANSITION_INDICATOR + '_'):]
                    istr, name = name.split('_', maxsplit=1)
                    i = int(istr)
                    if i < len(self.transitions):
                        self.transitions[i] = name
                    else:
                        # TODO: not sure what's going on here with check_bmc and pd.check_k_state_implication
                        # assert False
                        pass

        if allow_undefined:
            return

        def get_univ(d: SortDecl) -> List[str]:
            if d not in self.univs:
                self.univs[d] = [d.name + '0']
            return self.univs[d]

        def arbitrary_interp_r(r: RelationDecl) -> List[Tuple[List[str], bool]]:
            doms = [get_univ(syntax.get_decl_from_sort(s)) for s in r.arity]

            l = []
            tup: Tuple[str, ...]
            for tup in itertools.product(*doms):
                l.append((list(tup), False))

            return l

        def ensure_defined_r(r: RelationDecl) -> None:
            R: List[Dict[RelationDecl, List[Tuple[List[str], bool]]]]
            if not r.mutable:
                R = [self.immut_rel_interps]
            else:
                R = self.rel_interps
            interp: Optional[List[Tuple[List[str], bool]]] = None

            def get_interp() -> List[Tuple[List[str], bool]]:
                nonlocal interp
                if interp is None:
                    interp = arbitrary_interp_r(r)
                return interp

            for m in R:
                if r not in m:
                    m[r] = get_interp()

        def arbitrary_interp_c(c: ConstantDecl) -> str:
            sort = c.sort
            return get_univ(syntax.get_decl_from_sort(sort))[0]

        def ensure_defined_c(c: ConstantDecl) -> None:
            R: List[Dict[RelationDecl, List[Tuple[List[str], bool]]]]
            if not c.mutable:
                C = [self.immut_const_interps]
            else:
                C = self.const_interps

            interp: str = arbitrary_interp_c(c)

            for m in C:
                if c not in m:
                    m[c] = interp

        def arbitrary_interp_f(f: FunctionDecl) -> List[Tuple[List[str], str]]:
            doms = [get_univ(syntax.get_decl_from_sort(s)) for s in f.arity]

            interp = get_univ(syntax.get_decl_from_sort(f.sort))[0]

            l = []
            tup: Tuple[str, ...]
            for tup in itertools.product(*doms):
                l.append((list(tup), interp))

            return l

        def ensure_defined_f(f: FunctionDecl) -> None:
            F: List[Dict[FunctionDecl, List[Tuple[List[str], str]]]]
            if not f.mutable:
                F = [self.immut_func_interps]
            else:
                F = self.func_interps

            interp: Optional[List[Tuple[List[str], str]]] = None

            def get_interp() -> List[Tuple[List[str], str]]:
                nonlocal interp
                if interp is None:
                    interp = arbitrary_interp_f(f)
                return interp

            for m in F:
                if f not in m:
                    m[f] = get_interp()

        for decl in prog.relations_constants_and_functions():
            if isinstance(decl, RelationDecl):
                ensure_defined_r(decl)
            elif isinstance(decl, ConstantDecl):
                ensure_defined_c(decl)
            else:
                assert isinstance(decl, FunctionDecl)
                ensure_defined_f(decl)

    def as_diagram(self, i: Optional[int] = None, subclause_complete: Optional[bool] = None) -> Diagram:
        assert len(self.keys) == 1 or i is not None, \
            'to generate a diagram from a multi-state model, you must specify which state you want'
        assert i is None or (0 <= i and i < len(self.keys))

        if subclause_complete is None:
            subclause_complete = utils.args.diagrams_subclause_complete

        if i is None:
            i = 0

        if i not in self.diagram_cache:
            prog = syntax.the_program

            mut_rel_interps = self.rel_interps[i]
            mut_const_interps = self.const_interps[i]
            mut_func_interps = self.func_interps[i]

            vars_by_sort: Dict[SortDecl, List[syntax.SortedVar]] = OrderedDict()
            if subclause_complete:
                from networkx.utils.union_find import UnionFind  # type: ignore
                ufs: Dict[SortDecl, UnionFind] = {}
            ineqs: Dict[SortDecl, List[Expr]] = OrderedDict()
            rels: Dict[RelationDecl, List[Expr]] = OrderedDict()
            consts: Dict[ConstantDecl, Expr] = OrderedDict()
            funcs: Dict[FunctionDecl, List[Expr]] = OrderedDict()
            for sort in self.univs:
                vars_by_sort[sort] = [syntax.SortedVar(None, v, syntax.UninterpretedSort(None, sort.name))
                                      for v in self.univs[sort]]
                if subclause_complete:
                    ufs[sort] = UnionFind(self.univs[sort])
                    ineqs[sort] = []
                else:
                    u = [syntax.Id(None, s) for s in self.univs[sort]]
                    ineqs[sort] = [syntax.Neq(a, b) for a, b in itertools.combinations(u, 2)]

            for R, l in itertools.chain(mut_rel_interps.items(), self.immut_rel_interps.items()):
                rels[R] = []
                for tup, ans in l:
                    e: Expr
                    if len(tup) > 0:
                        args: List[Expr] = []
                        for (col, col_sort) in zip(tup, R.arity):
                            assert isinstance(col_sort, syntax.UninterpretedSort)
                            assert col_sort.decl is not None
                            if subclause_complete:
                                nm = col_sort.name + str(len(vars_by_sort[col_sort.decl]))
                                vars_by_sort[col_sort.decl].append(syntax.SortedVar(None, nm, col_sort))
                                arg = syntax.Id(None, nm)
                                args.append(arg)
                                ufs[col_sort.decl].union(col, nm)
                            else:
                                args.append(syntax.Id(None, col))
                        e = syntax.AppExpr(None, R.name, args)
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

            if subclause_complete:
                for sort, uf in ufs.items():
                    sets = list(uf.to_sets())
                    for s1, s2 in itertools.combinations(sets, 2):
                        for x1, x2 in itertools.product(s1, s2):
                            ineqs[sort].append(syntax.Neq(syntax.Id(None, x1), syntax.Id(None, x2)))
                    for s in sets:
                        for x1, x2 in itertools.combinations(s, 2):
                            ineqs[sort].append(syntax.Eq(syntax.Id(None, x1), syntax.Id(None, x2)))

            vs = list(itertools.chain(*(vs for vs in vars_by_sort.values())))
            diag = Diagram(vs, ineqs, rels, consts, funcs)
            if utils.args.simplify_diagram:
                diag.simplify_consts()
            assert prog.scope is not None
            diag.resolve(prog.scope)

            self.diagram_cache[i] = diag

        return self.diagram_cache[i]

    def as_onestate_formula(self, i: Optional[int] = None) -> Expr:
        assert len(self.keys) == 1 or i is not None, \
            'to generate a onestate formula from a multi-state model, ' + \
            'you must specify which state you want'
        assert i is None or (0 <= i and i < len(self.keys))

        if i is None:
            i = 0

        if i not in self.onestate_formula_cache:
            prog = syntax.the_program

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
                u = [syntax.Id(None, v) for v in self.univs[sort]]
                ineqs[sort] = [syntax.Neq(a, b) for a, b in itertools.combinations(u, 2)]
            for R, l in itertools.chain(mut_rel_interps.items(), self.immut_rel_interps.items()):
                rels[R] = []
                for tup, ans in l:
                    e = (
                        syntax.AppExpr(None, R.name, [syntax.Id(None, col) for col in tup])
                        if len(tup) > 0 else syntax.Id(None, R.name)
                    )
                    rels[R].append(e if ans else syntax.Not(e))
            for C, c in itertools.chain(mut_const_interps.items(), self.immut_const_interps.items()):
                consts[C] = syntax.Eq(syntax.Id(None, C.name), syntax.Id(None, c))
            for F, fl in itertools.chain(mut_func_interps.items(), self.immut_func_interps.items()):
                funcs[F] = [
                    syntax.Eq(syntax.AppExpr(None, F.name, [syntax.Id(None, col) for col in tup]),
                              syntax.Id(None, res))
                    for tup, res in fl
                ]

            # get a fresh variable, avoiding names of universe elements in vs
            fresh = prog.scope.fresh('x', [v.name for v in vs])

            e = syntax.Exists(vs, syntax.And(
                *itertools.chain(*ineqs.values(), *rels.values(), consts.values(), *funcs.values(), (
                    syntax.Forall([syntax.SortedVar(None, fresh,
                                                    syntax.UninterpretedSort(None, sort.name))],
                                  syntax.Or(*(syntax.Eq(syntax.Id(None, fresh), syntax.Id(None, v))
                                              for v in self.univs[sort])))
                    for sort in self.univs
                ))))
            assert prog.scope is not None
            e.resolve(prog.scope, None)
            self.onestate_formula_cache[i] = e
        return self.onestate_formula_cache[i]

    def as_state(self, i: Optional[int] = None) -> State:
        assert len(self.keys) == 1 or i is not None, \
            'to generate a State from a multi-state model, ' + \
            'you must specify which state you want'
        assert i is None or (0 <= i and i < len(self.keys))

        if i is None:
            i = 0

        return State(self.univs,
                     dict(itertools.chain(self.immut_rel_interps.items(), self.rel_interps[i].items())),
                     dict(itertools.chain(self.immut_const_interps.items(), self.const_interps[i].items())),
                     dict(itertools.chain(self.immut_func_interps.items(), self.func_interps[i].items())))

    def eval_double_vocab(self, full_expr: Expr, start_location: int) -> Union[str, bool]:
        def eval(expr: Expr, old: bool) -> Union[str, bool]:
            def current_index() -> int:
                return start_location + (1 if not old else 0)
            def current_rels() -> Dict[RelationDecl, List[Tuple[List[str], bool]]]:
                return dict(itertools.chain(self.immut_rel_interps.items(), self.rel_interps[current_index()].items()))
            def current_consts() -> Dict[ConstantDecl, str]:
                return dict(itertools.chain(self.immut_const_interps.items(), self.const_interps[current_index()].items()))
            def current_funcs() -> Dict[FunctionDecl, List[Tuple[List[str], str]]]:
                return dict(itertools.chain(self.immut_func_interps.items(), self.func_interps[current_index()].items()))
            scope: syntax.Scope[Union[str, bool]] = \
                cast(syntax.Scope[Union[str, bool]], syntax.the_program.scope)
            if isinstance(expr, syntax.Bool):
                return expr.val
            elif isinstance(expr, syntax.UnaryExpr):
                if expr.op == 'OLD':
                    return eval(expr.arg, old=True)
                elif expr.op == 'NOT':
                    return not eval(expr.arg, old)
                assert False, "eval unknown operation %s" % expr.op
            elif isinstance(expr, syntax.BinaryExpr):
                if expr.op == 'IMPLIES':
                    return not eval(expr.arg1, old) or eval(expr.arg2, old)
                elif expr.op in ['IFF', 'EQUAL']:
                    return eval(expr.arg1, old) == eval(expr.arg2, old)
                else:
                    assert expr.op == 'NOTEQ'
                    return eval(expr.arg1, old) != eval(expr.arg2, old)
            elif isinstance(expr, syntax.NaryExpr):
                assert expr.op in ['AND', 'OR', 'DISTINCT']
                if expr.op in ['AND', 'OR']:
                    p = all if expr.op == 'AND' else any
                    return p(eval(arg, old) for arg in expr.args)
                else:
                    assert expr.op == 'DISTINCT'
                    return len(set(eval(arg, old) for arg in expr.args)) == len(expr.args)
            elif isinstance(expr, syntax.AppExpr):
                d = scope.get(expr.callee)
                assert isinstance(d, syntax.RelationDecl) or isinstance(d, syntax.FunctionDecl)
                table: Sequence[Tuple[Sequence[str], Union[bool, str]]]
                if isinstance(d, syntax.RelationDecl):
                    # TODO: replace the following line due to pickling non-uniqueness of RelationDecl
                    # table = self.rel_interp[d]
                    interp_from_name = dict((r.name, interp) for (r, interp) in current_rels().items())
                    table = interp_from_name[d.name]
                else:
                    # TODO: replace the following line due to pickling non-uniqueness of FunctionDecl
                    # table = current_funcs()[d]
                    interp_from_name = dict((r.name, interp) for (r, interp) in current_funcs().items())
                    table = interp_from_name[d.name]
                args = []
                for arg in expr.args:
                    ans = eval(arg, old)
                    assert isinstance(ans, str)
                    args.append(ans)
                return _lookup_assoc(table, args)
            elif isinstance(expr, syntax.QuantifierExpr):
                assert expr.quant in ['FORALL', 'EXISTS']
                p = all if expr.quant == 'AND' else any
                # TODO: replaced the following line due to pickling non-uniqueness of SortDecl
                # doms = [self.univs[syntax.get_decl_from_sort(sv.sort)] for sv in expr.binder.vs]
                univs_from_str = dict((s.name, univ) for (s, univ) in self.univs.items())
                assert all(isinstance(sv.sort, syntax.UninterpretedSort) for sv in expr.binder.vs)
                doms = [univs_from_str[cast(syntax.UninterpretedSort, sv.sort).name] for sv in expr.binder.vs]

                def one(q: syntax.QuantifierExpr, tup: Tuple[str, ...]) -> bool:
                    with scope.in_scope(q.binder, list(tup)):
                        ans = eval(q.body, old)
                        assert isinstance(ans, bool)
                        return ans
                return p(one(expr, t) for t in itertools.product(*doms))
            elif isinstance(expr, syntax.Id):
                a = scope.get(expr.name)
                # definitions are not supported
                assert not isinstance(a, syntax.DefinitionDecl) and not isinstance(a, syntax.FunctionDecl) and a is not None
                if isinstance(a, syntax.RelationDecl):
                    return _lookup_assoc(current_rels()[a], [])
                elif isinstance(a, syntax.ConstantDecl):
                    return current_consts()[a]
                elif isinstance(a, tuple):
                    # bound variable introduced to scope
                    (bound_elem,) = a
                    return bound_elem
                else:
                    assert isinstance(a, str) or isinstance(a, bool)
                    return a
            elif isinstance(expr, syntax.IfThenElse):
                branch = eval(expr.branch, old)
                assert isinstance(branch, bool)
                return eval(expr.then, old) if branch else eval(expr.els, old)
            elif isinstance(expr, syntax.Let):
                val = eval(expr.val, old)
                with scope.in_scope(expr.binder, [val]):
                    return eval(expr.bod, old)
            else:
                assert False, expr

        return eval(full_expr, old=False)

_K = TypeVar('_K')
_V = TypeVar('_V')

def _lookup_assoc(l: Sequence[Tuple[_K, _V]], k: _K) -> _V:
    for k2, v2 in l:
        if k == k2:
            return v2
    assert False

@dataclass
class State(object):
    univs: Dict[SortDecl, List[str]]
    rel_interp: Dict[RelationDecl, List[Tuple[List[str], bool]]]
    const_interp: Dict[ConstantDecl, str]
    func_interp: Dict[FunctionDecl, List[Tuple[List[str], str]]]

    def __str__(self) -> str:
        l = []
        l.extend(univ_str(self))
        l.append(_state_str(self, self.const_interp, self.rel_interp, self.func_interp))
        return '\n'.join(l)

    # TODO: eliminate duplication with trace.eval_double_vocab
    def eval(self, expr: Expr) -> Union[str, bool]:
        scope: syntax.Scope[Union[str, bool]] = \
            cast(syntax.Scope[Union[str, bool]], syntax.the_program.scope)
        if isinstance(expr, syntax.Bool):
            return expr.val
        elif isinstance(expr, syntax.UnaryExpr):
            assert expr.op != 'OLD', "cannot eval 'old' in a single state"
            assert expr.op == 'NOT'
            return not self.eval(expr.arg)
        elif isinstance(expr, syntax.BinaryExpr):
            if expr.op == 'IMPLIES':
                return not self.eval(expr.arg1) or self.eval(expr.arg2)
            elif expr.op in ['IFF', 'EQUAL']:
                return self.eval(expr.arg1) == self.eval(expr.arg2)
            else:
                assert expr.op == 'NOTEQ'
                return self.eval(expr.arg1) != self.eval(expr.arg2)
        elif isinstance(expr, syntax.NaryExpr):
            assert expr.op in ['AND', 'OR', 'DISTINCT']
            if expr.op in ['AND', 'OR']:
                p = all if expr.op == 'AND' else any
                return p(self.eval(arg) for arg in expr.args)
            else:
                assert expr.op == 'DISTINCT'
                return len(set(self.eval(arg) for arg in expr.args)) == len(expr.args)
        elif isinstance(expr, syntax.AppExpr):
            d = scope.get(expr.callee)
            assert isinstance(d, syntax.RelationDecl) or isinstance(d, syntax.FunctionDecl)
            table: Sequence[Tuple[Sequence[str], Union[bool, str]]]
            if isinstance(d, syntax.RelationDecl):
                # TODO: replace the following line due to pickling non-uniqueness of RelationDecl
                # table = self.rel_interp[d]
                interp_from_name = dict((r.name, interp) for (r, interp) in self.rel_interp.items())
                table = interp_from_name[d.name]
            else:
                table = self.func_interp[d]
            args = []
            for arg in expr.args:
                ans = self.eval(arg)
                assert isinstance(ans, str)
                args.append(ans)
            return _lookup_assoc(table, args)
        elif isinstance(expr, syntax.QuantifierExpr):
            assert expr.quant in ['FORALL', 'EXISTS']
            p = all if expr.quant == 'AND' else any
            # TODO: replaced the following line due to pickling non-uniqueness of SortDecl
            # doms = [self.univs[syntax.get_decl_from_sort(sv.sort)] for sv in expr.binder.vs]
            univs_from_str = dict((s.name, univ) for (s, univ) in self.univs.items())
            assert all(isinstance(sv.sort, syntax.UninterpretedSort) for sv in expr.binder.vs)
            doms = [univs_from_str[cast(syntax.UninterpretedSort, sv.sort).name] for sv in expr.binder.vs]

            def one(q: syntax.QuantifierExpr, tup: Tuple[str, ...]) -> bool:
                with scope.in_scope(q.binder, list(tup)):
                    ans = self.eval(q.body)
                    assert isinstance(ans, bool)
                    return ans
            return p(one(expr, t) for t in itertools.product(*doms))
        elif isinstance(expr, syntax.Id):
            a = scope.get(expr.name)
            # definitions are not supported
            assert not isinstance(a, syntax.DefinitionDecl) and not isinstance(a, syntax.FunctionDecl) and a is not None
            if isinstance(a, syntax.RelationDecl):
                return _lookup_assoc(self.rel_interp[a], [])
            elif isinstance(a, syntax.ConstantDecl):
                return self.const_interp[a]
            elif isinstance(a, tuple):
                # bound variable introduced to scope
                (bound_elem,) = a
                return bound_elem
            else:
                assert isinstance(a, str) or isinstance(a, bool)
                return a
        elif isinstance(expr, syntax.IfThenElse):
            branch = self.eval(expr.branch)
            assert isinstance(branch, bool)
            return self.eval(expr.then) if branch else self.eval(expr.els)
        elif isinstance(expr, syntax.Let):
            val = self.eval(expr.val)
            with scope.in_scope(expr.binder, [val]):
                return self.eval(expr.body)
        else:
            assert False, expr

    def element_sort(self, element_name: str) -> SortDecl:
        matching_sorts = [sort for (sort, univ) in self.univs.items()
                          if element_name in univ]
        assert matching_sorts, "%s unknown element name" % element_name
        assert len(matching_sorts) == 1, "ambiguous element name %s" % element_name
        return matching_sorts[0]

class Blocked(object):
    pass
class CexFound(object):
    pass
class GaveUp(object):
    pass
5