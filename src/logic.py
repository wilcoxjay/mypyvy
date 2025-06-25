from __future__ import annotations
from collections import OrderedDict, defaultdict
from contextlib import contextmanager
from datetime import datetime
import itertools
import math
import random
import sys
from typing import List, Optional, Set, Tuple, Union, Iterable, Dict, Iterator
from typing import Callable

import z3

import utils
import typechecker
import syntax
from syntax import Expr, Scope, ConstantDecl, RelationDecl, SortDecl
from syntax import FunctionDecl, DefinitionDecl, Not, New
from semantics import Trace, State, FirstOrderStructure
from translator import Z3Translator, TRANSITION_INDICATOR
import solver
from solver import Solver
import parser

class SolverReturnedUnknown(Exception):
    def __init__(self, message: Optional[str] = None) -> None:
        super().__init__(message)

def check_solver(s: Solver, num_states: int, minimize: Optional[bool] = None) -> Optional[Trace]:
    res = s.check()
    m = None

    if res != solver.unsat:
        if res != solver.sat:
            assert res == solver.unknown
            utils.logger.always_print('unknown!')
            reason = s.reason_unknown()
            utils.logger.always_print('reason unknown: ' + reason)
            raise SolverReturnedUnknown(reason)

        assert res == solver.sat
        m = Z3Translator.model_to_trace(s.model(minimize=minimize), num_states)

    return m

def check_unsat(
        errmsgs: List[Tuple[Optional[syntax.Span], str]],
        s: Solver,
        num_states: int,
        minimize: Optional[bool] = None,
        verbose: bool = True,
        print_no: bool = True,
) -> Optional[Trace]:
    start = datetime.now()
    # if logger.isEnabledFor(logging.DEBUG):
    #     logger.debug('assertions')
    #     logger.debug(str(s.assertions()))

    if (m := check_solver(s, num_states, minimize=minimize)) is not None:
        if verbose:
            if print_no:
                utils.logger.always_print('no!')
            if utils.args.print_counterexample:
                utils.logger.always_print('\ncounterexample:')
                utils.logger.always_print(utils.indent(str(m)))
                if len(errmsgs) > 0:
                    utils.logger.always_print('')

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
                                           (ition.span, 'transition %s does not preserve invariant%s'
                                            % (ition.name, msg))],
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
                res = s.check()
                assert res in (solver.sat, solver.unsat), res
                if res != solver.unsat:
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
                assert res in (solver.sat, solver.unsat), res
                if res != solver.unsat:
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


def check_theorem(th: syntax.TheoremDecl, s: Solver,
                  errmsgs: List[Tuple[Optional[syntax.Span], str]] = [],
                  verbose: bool = True) -> Optional[Trace]:
    if th.num_states == 2:
        num_states = 2
    elif th.num_states == 1:
        num_states = 1
    else:
        num_states = 0

    t = s.get_translator(num_states)

    with s.new_frame():
        s.add(t.translate_expr(Not(th.expr)))

        return check_unsat(errmsgs, s, num_states, verbose=verbose)


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
        if res == solver.sat:
            z3m = s.model(minimize=minimize)
            m = Z3Translator.model_to_trace(z3m, depth + 1)
            return m
        elif res == solver.unknown:
            print('unknown!')
        return None


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
            List[syntax.SortedVar],  # vs
            Dict[SortDecl, List[Expr]],  # ineqs
            Dict[RelationDecl, List[Expr]],  # rels
            Dict[ConstantDecl, Expr],  # consts
            Dict[FunctionDecl, List[Expr]],  # funcs
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

def parse_and_typecheck_expr(input: str, n_states: int = 0, close_free_vars: bool = False) -> syntax.Expr:
    e = parser.parse_expr(input)
    if close_free_vars:
        e = syntax.close_free_vars(e, span=e.span)

    scope = syntax.the_program.scope
    with scope.n_states(n_states):
        typechecker.typecheck_expr(scope, e, None)
    return e
