from __future__ import annotations
from collections import OrderedDict, defaultdict
from contextlib import contextmanager
from datetime import datetime
import itertools
import io
import logging
import sys
from typing import List, Any, Optional, Set, Tuple, Union, Iterable, Dict, Sequence, Iterator, \
    cast
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
) -> z3.CheckSatResult:
    start = datetime.now()
    # if logger.isEnabledFor(logging.DEBUG):
    #     logger.debug('assertions')
    #     logger.debug(str(s.assertions()))

    res = s.check()
    if res != z3.unsat:
        if res == z3.sat:
            m = Model.from_z3(keys, s.model())

            utils.logger.always_print('')
            if utils.args.print_counterexample:
                utils.logger.always_print(str(m))
        else:
            assert res == z3.unknown
            utils.logger.always_print('unknown!')
            utils.logger.always_print('reason unknown: ' + s.reason_unknown())
        for tok, msg in errmsgs:
            utils.print_error(tok, msg)
    else:

        if not utils.args.query_time:
            time_msg = ''
        else:
            time_msg = ' (%s)' % (datetime.now() - start, )
        utils.logger.always_print('ok.%s' % (time_msg,))

        sys.stdout.flush()

    return res

@utils.log_start_end_xml(utils.logger, logging.INFO)
def check_init(s: Solver, safety_only: bool = False) -> None:
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

                check_unsat([(inv.tok, 'invariant%s may not hold in initial state' % msg)],
                            s, [KEY_ONE])


def check_transitions(s: Solver) -> None:
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

                        check_unsat([(inv.tok, 'invariant%s may not be preserved by transition %s'
                                      % (msg, trans.name)),
                                     (trans.tok, 'this transition may not preserve invariant%s'
                                      % (msg,))],
                                    s, [KEY_OLD, KEY_NEW])

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
                # if utils.logger.isEnabledFor(logging.DEBUG):
                #     utils.logger.debug('assertions')
                #     utils.logger.debug(str(s.assertions()))

                if s.check() != z3.unsat:
                    return s.model()

    return None

def check_two_state_implication_all_transitions(
        s: Solver,
        old_hyps: Iterable[Expr],
        new_conc: Expr
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

                if s.check() != z3.unsat:
                    return s.model(), trans

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
        s.add(tid == t.translate_transition(transition))

    if allow_stutter:
        tid = z3.Bool(get_transition_indicator(uid, 'stutter'))
        tids.append(tid)
        s.add(tid == z3.And(*t.frame([])))

    s.add(z3.Or(*tids))

def check_bmc(s: Solver, safety: Expr, depth: int) -> None:
    keys = ['state%2d' % i for i in range(depth + 1)]
    prog = syntax.the_program

    if utils.logger.isEnabledFor(logging.DEBUG):
        utils.logger.debug('check_bmc property: %s' % safety)
        utils.logger.debug('check_bmc depth: %s' % depth)

    for k in keys:
        s.get_translator(k)  # initialize all the keys before pushing a solver stack frame

    with s:
        t = s.get_translator(keys[0])
        for init in prog.inits():
            s.add(t.translate_expr(init.expr))

        t = s.get_translator(keys[-1])
        s.add(t.translate_expr(syntax.Not(safety)))

        for i in range(depth):
            assert_any_transition(s, str(i), keys[i + 1], keys[i], allow_stutter=True)

        # if utils.logger.isEnabledFor(logging.DEBUG):
        #     utils.logger.debug('assertions')
        #     utils.logger.debug(str(s.assertions()))

        check_unsat([(None, 'found concrete trace violating safety')],
                    s, keys)

def check_two_state_implication_along_transitions(
        s: Solver,
        old_hyps: Iterable[Expr],
        transitions: Sequence[PhaseTransition],
        new_conc: Expr
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
                    return s.model(), phase_transition

    return None


class Solver(object):
    def __init__(self) -> None:
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

        self.register_mutable_axioms(r.derived_axiom for r in prog.derived_relations()
                                     if r.derived_axiom is not None)

        t = self.get_translator()
        for a in prog.axioms():
            self.add(t.translate_expr(a.expr))

    def register_mutable_axioms(self, axioms: Iterable[Expr]) -> None:
        assert len(self.known_keys) == 0, \
            "mutable axioms must be registered before any keys are known to the solver!"
        self.mutable_axioms.extend(axioms)

    def _initialize_key(self, key: Optional[str]) -> None:
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

    def check(self, assumptions: Optional[Sequence[z3.ExprRef]] = None) -> z3.CheckSatResult:
        # logger.debug('solver.check')
        if assumptions is None:
            assert not self.assumptions_necessary
            assumptions = []
        self.nqueries += 1
        return self.z3solver.check(*assumptions)

    def model(self, assumptions: Optional[Sequence[z3.ExprRef]] = None) -> z3.ModelRef:
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
        # logger.debug(str(Model(m, KEY_NEW, KEY_OLD)))
        # logger.debug('assertions')
        # logger.debug(str(self.assertions()))

        with self:
            for s in m.sorts():
                for n in itertools.count(1):
                    with self:
                        self.add(self._cardinality_constraint(s, n))
                        res = self.check(assumptions)
                        if res == z3.sat:
                            break
                self.add(self._cardinality_constraint(s, n))
            assert self.check(assumptions) == z3.sat

            # # TODO: ODED: there's actually a similar problem here too,
            # # but I don't fix it now since there's anyway something
            # # funny happening with n < 2
            # for d in m.decls():
            #     nm = d.name()
            #     if nm.startswith(KEY_OLD) or nm.startswith(KEY_ONE):
            #         arity = d.arity()
            #         if arity == 1 and d.range() == z3.BoolSort():
            #             s = d.domain(0)
            #             u = m.get_universe(s)
            #             hi = sum(1 if m.eval(d(x)) else 0 for x in u)
            #             n = 1
            #             while n < hi and n < 2:  # hehe
            #                 with self:
            #                     self.add(self._relational_cardinality_constraint(d, n))
            #                     res = self.check(assumptions)
            #                     if res == z3.sat:
            #                         break
            #                 n += 1
            #             if n < hi and n < 2:
            #                 self.add(self._relational_cardinality_constraint(d, n))
            # assert self.check(assumptions) == z3.sat
            m = self.z3solver.model()
            # logger.debug('finished with minimal model')
            # logger.debug(str(Model(m, KEY_NEW, KEY_OLD)))
            return m

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
        self.tombstones: Dict[_RelevantDecl, Optional[Set[int]]] = defaultdict(lambda: set())

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

    def conjuncts_simple(self) -> Iterable[Tuple[_RelevantDecl, int, Expr]]:
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
    def valid_in_init(self, s: Solver) -> Optional[z3.ModelRef]:
        prog = syntax.the_program
        return check_implication(s, (init.expr for init in prog.inits()),
                                 [syntax.Not(self.to_ast())])

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
            propagate_init: bool) -> Optional[z3.ModelRef]:
        for src, transitions in transitions_to_grouped_by_src.items():
            ans = check_two_state_implication_along_transitions(
                s, f.summary_of(src), transitions, syntax.Not(self.to_ast()))
            if ans is not None:
                return ans[0]

        if propagate_init:
            return self.valid_in_init(s)
        return None

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
                        s, f, transitions_to_grouped_by_src, propagate_init)
                if res is None:
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
                            s, f, transitions_to_grouped_by_src, propagate_init)
                    if res is None:
                        if utils.logger.isEnabledFor(logging.DEBUG):
                            utils.logger.debug(f'eliminated all negative conjuncts from decl {d}')
                        self.remove_clause(d, cs)
                        self.smoke(s, depth)

            for d, j, c in self.conjuncts():
                with self.without(d, j):
                    res = self.check_valid_in_phase_from_frame(
                        s, f, transitions_to_grouped_by_src, propagate_init)
                if res is None:
                    if utils.logger.isEnabledFor(logging.DEBUG):
                        utils.logger.debug('eliminated clause %s' % c)
                    self.remove_clause(d, j)
                    self.smoke(s, depth)

        self.prune_unused_vars()

        if utils.logger.isEnabledFor(logging.DEBUG):
            utils.logger.debug('generalized diag')
            utils.logger.debug(str(self))

class Model(object):
    def __init__(
            self,
            keys: List[str],
    ) -> None:
        self.z3model: Optional[z3.ModelRef] = None
        self.keys = keys

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

    @staticmethod
    def from_z3(keys: List[str], z3m: z3.ModelRef) -> Model:
        m = Model(keys)
        m.z3model = z3m
        m.read_out(z3m)
        return m

    def try_printed_by(self, s: SortDecl, elt: str) -> Optional[str]:
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
                return custom_printer(self, s, elt, custom_printer_args)
            else:
                utils.print_warning(custom_printer_annotation.tok,
                                    'could not find printer named %s' % (printer_name,))
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
        l.append(self._state_str(self.immut_const_interps, self.immut_rel_interps,
                                 self.immut_func_interps))
        for i, k in enumerate(self.keys):
            if i > 0 and self.transitions[i - 1] != '':
                l.append('\ntransition %s' % (self.transitions[i - 1],))
            l.append('\nstate %s:' % (i,))
            l.append(self._state_str(self.const_interps[i], self.rel_interps[i],
                                     self.func_interps[i]))

        return '\n'.join(l)

    def _state_str(
            self,
            Cs: Dict[ConstantDecl, str],
            Rs: Dict[RelationDecl, List[Tuple[List[str], bool]]],
            Fs: Dict[FunctionDecl, List[Tuple[List[str], str]]]
    ) -> str:
        l = []
        for C in Cs:
            if syntax.has_annotation(C, 'no_print'):
                continue
            l.append('%s = %s' % (C.name, self.print_element(C.sort, Cs[C])))

        for R in Rs:
            if syntax.has_annotation(R, 'no_print'):
                continue
            for tup, b in sorted(Rs[R], key=lambda x: self.print_tuple(R.arity, x[0])):
                if b:
                    l.append('%s%s(%s)' % ('' if b else '!', R.name,
                                           self.print_tuple(R.arity, tup)))

        for F in Fs:
            if syntax.has_annotation(F, 'no_print'):
                continue
            for tup, res in sorted(Fs[F], key=lambda x: self.print_tuple(F.arity, x[0])):
                l.append('%s(%s) = %s' % (F.name, self.print_tuple(F.arity, tup),
                                          self.print_element(F.sort, res)))

        return '\n'.join(l)

    def read_out(self, z3model: z3.ModelRef) -> None:
        # utils.logger.debug('read_out')
        def rename(s: str) -> str:
            return s.replace('!val!', '')

        def _eval(expr: z3.ExprRef) -> z3.ExprRef:
            ans = z3model.eval(expr, model_completion=True)
            assert bool(ans) is True or bool(ans) is False, (expr, ans)
            return ans

        prog = syntax.the_program

        self.univs: Dict[SortDecl, List[str]] = OrderedDict()
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
                    self.transitions[i] = name

    def as_diagram(self, i: Optional[int] = None) -> Diagram:
        assert len(self.keys) == 1 or i is not None, \
            'to generate a diagram from a multi-state model, you must specify which state you want'
        assert i is None or (0 <= i and i < len(self.keys))

        if i is None:
            i = 0

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

            u = [syntax.Id(None, s) for s in self.univs[sort]]
            ineqs[sort] = [syntax.Neq(a, b) for a, b in itertools.combinations(u, 2)]

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
        assert prog.scope is not None
        diag.resolve(prog.scope)

        return diag

    def as_onestate_formula(self, i: Optional[int] = None) -> Expr:
        assert len(self.keys) == 1 or i is not None, \
            'to generate a onestate formula from a multi-state model, ' + \
            'you must specify which state you want'
        assert i is None or (0 <= i and i < len(self.keys))

        if i is None:
            i = 0

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
        return e

class Blocked(object):
    pass
class CexFound(object):
    pass
class GaveUp(object):
    pass
