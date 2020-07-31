import dataclasses
from dataclasses import dataclass
import z3

import utils
from utils import MySet
import logic
from logic import Solver, Diagram, Trace, State
import syntax
from syntax import Expr, TrueExpr, DefinitionDecl, New
import pickle
from typing import List, Optional, Tuple, Union, Sequence
from translator import Z3Translator

RelaxedTrace = List[Tuple[Optional[DefinitionDecl], Union[Diagram, Expr]]]

class AbstractCounterexample(Exception):
    pass

def equiv_expr(solver: Solver, e1: Expr, e2: Expr) -> bool:
    return (logic.check_implication(solver, [e1], [e2], minimize=False) is None and
            logic.check_implication(solver, [e2], [e1], minimize=False) is None)

class Frame:
    def __init__(self, summary: Optional[Sequence[Expr]] = None) -> None:
        if summary is None:
            summary = [TrueExpr]
        self._summary = MySet(summary)

    def summary(self) -> Sequence[Expr]:
        return self._summary.l

    def strengthen(self, conjunct: Expr) -> None:
        self._summary.add(conjunct)

    def __str__(self) -> str:
        return str([str(x) for x in self._summary])


@dataclass
class BackwardReachableState:
    id: int
    state_or_expr: Union[State, Expr]
    num_steps_to_bad: int
    known_absent_until_frame: int = dataclasses.field(default=0, init=False)

def negate_clause(c: Expr) -> Expr:
    if isinstance(c, syntax.Bool):
        return syntax.Bool(not c.val)
    elif isinstance(c, syntax.UnaryExpr):
        assert c.op == 'NOT'
        return c.arg
    elif isinstance(c, syntax.BinaryExpr):
        assert c.op in ['EQUAL', 'NOTEQ']
        op = 'NOTEQ' if c.op == 'EQUAL' else 'EQUAL'
        return syntax.BinaryExpr(op, c.arg1, c.arg2)
    elif isinstance(c, syntax.NaryExpr):
        assert c.op == 'OR'
        return syntax.NaryExpr('AND', [negate_clause(arg) for arg in c.args])
    elif isinstance(c, syntax.AppExpr) or isinstance(c, syntax.Id):
        return syntax.Not(c)
    elif isinstance(c, syntax.QuantifierExpr):
        assert c.quant == 'FORALL'
        return syntax.QuantifierExpr('EXISTS', c.vs(), negate_clause(c.body))
    else:
        assert False, f'unsupported expression {c} in negate_clause'

class Frames:
    def __init__(self, solver: Solver) -> None:
        self.solver = solver
        self.fs: List[Frame] = []
        self.predicates: List[Expr] = []
        self.safeties = []
        self.backwards_reachable_states: List[BackwardReachableState] = []
        self.currently_blocking: Optional[BackwardReachableState] = None

        for inv in syntax.the_program.safeties():
            try:
                cs = syntax.as_clauses(inv.expr)
                utils.logger.info(f'converted safety {inv.expr} in to clauses:')
                for c in cs:
                    d = negate_clause(c)
                    utils.logger.info(str(d))
                    self.record_backwards_reachable_state(
                        BackwardReachableState(
                            len(self.backwards_reachable_states),
                            d,
                            0
                        )
                    )
            except Exception:
                self.safeties.append(inv.expr)

        self._first_frame()

    def __getitem__(self, i: int) -> Frame:
        return self.fs[i]

    def __setitem__(self, i: int, e: Frame) -> None:
        assert e is self.fs[i]

    def __len__(self) -> int:
        return len(self.fs)

    def _first_frame(self) -> None:
        init_conjuncts = [init.expr for init in syntax.the_program.inits()]
        self.new_frame(init_conjuncts)

    def new_frame(self, contents: Optional[Sequence[Expr]] = None) -> None:
        utils.logger.info(f'starting frame {len(self.fs)}')
        self.fs.append(Frame(contents))
        self.push_forward_frames()

    def establish_safety(self) -> None:
        while bstate := self.find_something_to_block():
            self.currently_blocking = bstate
            if isinstance(state := bstate.state_or_expr, State):
                diag_or_expr: Union[Diagram, Expr] = state.as_diagram()
            else:
                assert isinstance(expr := bstate.state_or_expr, Expr)
                diag_or_expr = expr
            frame_no = bstate.known_absent_until_frame + 1
            utils.logger.info(f'will block state #{bstate.id} in frame {frame_no}')
            self.block(diag_or_expr, frame_no, [(None, diag_or_expr)])
            bstate.known_absent_until_frame += 1

    def find_something_to_block(self) -> Optional[BackwardReachableState]:
        utils.logger.info('looking for something to block')

        while True:
            # for bstate in self.backwards_reachable_states:
            #     utils.logger.info(f'#{bstate.id} valid_up_to={bstate.known_absent_until_frame} '
            #                       f'steps_to_bad={bstate.num_steps_to_bad}')

            bstate_min = min(self.backwards_reachable_states,
                             key=lambda b: (b.known_absent_until_frame, b.num_steps_to_bad),
                             default=None)

            if bstate_min is None or (min_frame_no := bstate_min.known_absent_until_frame) == len(self) - 1:
                break

            if isinstance(state := bstate_min.state_or_expr, State):
                eval_res = state.eval(syntax.And(*(self[min_frame_no + 1].summary())))
                assert isinstance(eval_res, bool)
                if eval_res:
                    return bstate_min
            else:
                expr = state
                res = logic.check_implication(self.solver,
                                              self[min_frame_no + 1].summary(),
                                              [syntax.Not(expr)],
                                              minimize=False)
                if res is not None:
                    return bstate_min

            bstate_min.known_absent_until_frame += 1

        utils.logger.info('no existing states to block. looking for a new state.')

        f = self.fs[-1]
        if len(self.safeties) == 0 or (res := logic.check_implication(self.solver, f.summary(), self.safeties)) is None:
            utils.logger.info('frontier is safe. nothing new to block either.')
            return None

        state = Z3Translator.model_to_trace(res, 1).as_state(0)
        assert len(self) >= 2
        bstate = BackwardReachableState(len(self.backwards_reachable_states), state, 0)
        bstate.known_absent_until_frame = len(self) - 2
        self.record_backwards_reachable_state(bstate)
        return bstate

    def record_backwards_reachable_state(self, state: BackwardReachableState) -> None:
        utils.logger.info(f'discovered state #{len(self.backwards_reachable_states)}')
        utils.logger.info(str(state))
        self.backwards_reachable_states.append(state)

    def get_inductive_frame(self) -> Optional[Frame]:
        for i in range(len(self) - 1):
            if self.is_frame_inductive(i):
                return self[i + 1]
        return None

    def is_frame_inductive(self, i: int) -> bool:
        res = logic.check_implication(self.solver, self[i + 1].summary(), self[i].summary(), minimize=False)
        return res is None

    def push_conjunct(self, frame_no: int, c: Expr) -> bool:
        f = self.fs[frame_no]
        if self.clause_implied_by_transitions_from_frame(f, c, minimize=False) is None:
            self[frame_no + 1].strengthen(c)
            return True
        return False

    def push_forward_frames(self) -> None:
        for i, f in enumerate(self.fs[:-1]):
            self.push_frame(i, f)

    def always_assert_inductive_trace(self) -> None:
        for i, f in enumerate(self.fs[:-1]):
            for c in self.fs[i + 1].summary():
                res = self.clause_implied_by_transitions_from_frame(f, c, Solver())
                assert res is None, ("Non inductive trace:\n\t%s\n\t%s" % (c, f))

    def push_frame(self, i: int, f: Frame) -> None:
        conjuncts = f._summary
        j = 0
        while j < len(conjuncts):
            c = conjuncts.l[j]
            if c not in self.fs[i + 1]._summary:
                self.push_conjunct(i, c)
            j += 1

    def block(
            self,
            diag_or_expr: Union[Diagram, Expr],
            j: int,
            trace: RelaxedTrace
    ) -> None:
        utils.logger.info(f'block({j})')

        def as_expr() -> Expr:
            return diag_or_expr.to_ast() if isinstance(diag_or_expr, Diagram) else diag_or_expr

        if j == 0 or (j == 1 and not self.valid_in_initial_frame(syntax.Not(as_expr()))):
            utils.logger.always_print('\n'.join(((t.name + ' ') if t is not None else '') +
                                                str(diag) for t, diag in trace))
            print('abstract counterexample: the system has no universal inductive invariant proving safety')
            if utils.args.checkpoint_out:
                self.store_frames(utils.args.checkpoint_out)
            raise AbstractCounterexample()

        while True:
            res, x = self.find_predecessor(j - 1, diag_or_expr)
            if res == z3.unsat:
                assert x is None or isinstance(x, MySet)
                core: Optional[MySet[int]] = x
                self.augment_core_for_init(diag_or_expr, core)
                break
            assert isinstance(x, tuple), (res, x)
            trans, cti = x
            pre_diag = cti.as_diagram(index=0)

            trace.append((trans, pre_diag))
            self.block(pre_diag, j - 1, trace)
            trace.pop()

        if isinstance(diag_or_expr, Diagram):
            diag_or_expr.minimize_from_core(core)

        def prev_frame_constraint(diag: Diagram) -> bool:
            pre_frame = self[j - 1].summary()
            return (
                logic.check_two_state_implication_all_transitions(
                    self.solver, pre_frame, syntax.Not(diag.to_ast()), minimize=False
                ) is None and
                self.valid_in_initial_frame(syntax.Not(diag.to_ast()))
            )

        if isinstance(diag_or_expr, Diagram):
            diag_or_expr.generalize(self.solver, prev_frame_constraint)
        e = syntax.Not(as_expr())
        utils.logger.info(f'block({j}) using {e}')
        self.add(e, j)
        k = j
        while k + 1 < len(self) and self.push_conjunct(k, e):
            utils.logger.info(f'and pushed to {k + 1}')
            k += 1

    def valid_in_initial_frame(self, e: Expr) -> bool:
        return logic.check_implication(self.solver, self.fs[0].summary(), [e], minimize=False) is None

    def augment_core_for_init(self, diag_or_expr: Union[Diagram, Expr], core: Optional[MySet[int]]) -> None:
        if core is None or not utils.args.use_z3_unsat_cores:
            return

        if not isinstance(diag := diag_or_expr, Diagram):
            return

        t = self.solver.get_translator(1)

        with self.solver.new_frame():
            for init in self.fs[0].summary():
                self.solver.add(t.translate_expr(init))

            self.solver.add(diag.to_z3(t))

            res = self.solver.check(diag.trackers)

            assert res == z3.unsat
            uc = self.solver.unsat_core()

            res = self.solver.check([diag.trackers[i] for i in core])
            if res == z3.unsat:
                return

            for x in sorted(uc, key=lambda y: y.decl().name()):
                assert isinstance(x, z3.ExprRef)
                core.add(int(x.decl().name()[1:]))

    def add(self, e: Expr, depth: Optional[int] = None) -> None:
        if depth is None:
            depth = len(self)

        for i in range(depth + 1):
            self[i].strengthen(e)

    def find_predecessor(
            self,
            j: int,
            diag_or_expr: Union[Diagram, Expr]
    ) -> Tuple[z3.CheckSatResult, Union[Optional[MySet[int]], Tuple[DefinitionDecl, Trace]]]:
        pre_frame = self[j]
        prog = syntax.the_program
        solver = self.solver
        t = self.solver.get_translator(2)

        if utils.args.use_z3_unsat_cores:
            core: Optional[MySet[int]] = MySet()
        else:
            core = None

        def to_z3() -> z3.ExprRef:
            if isinstance(diag_or_expr, Diagram):
                return diag_or_expr.to_z3(t, new=True)
            else:
                return t.translate_expr(New(diag_or_expr))

        def trackers() -> List[z3.ExprRef]:
            if isinstance(diag_or_expr, Diagram):
                return diag_or_expr.trackers
            else:
                return []

        with solver.new_frame(), solver.mark_assumptions_necessary():
            for f in pre_frame.summary():
                solver.add(t.translate_expr(f))
            solver.add(to_z3())
            for ition in prog.transitions():
                with solver.new_frame():
                    solver.add(t.translate_expr(ition.as_twostate_formula(prog.scope)))
                    if (res := solver.check(trackers())) == z3.sat:
                        m = Z3Translator.model_to_trace(solver.model(trackers()), 2)
                        state = m.as_state(0)
                        src = self.currently_blocking
                        assert src is not None
                        steps_from_cex = src.known_absent_until_frame + 1 - j + src.num_steps_to_bad
                        bstate = BackwardReachableState(len(self.backwards_reachable_states), state, steps_from_cex)
                        self.record_backwards_reachable_state(bstate)
                        return (z3.sat, (ition, m))
                    elif res == z3.unsat:
                        if utils.args.use_z3_unsat_cores and isinstance(diag_or_expr, Diagram):
                            assert core is not None
                            # carefully retrieve the unsat core before calling check again
                            uc = solver.unsat_core()
                            res = solver.check([diag_or_expr.trackers[i] for i in core])
                            if res == z3.unsat:
                                continue
                            for x in sorted(uc, key=lambda y: y.decl().name()):
                                assert isinstance(x, z3.ExprRef)
                                core.add(int(x.decl().name()[1:]))
                    else:
                        for e in solver.assertions():
                            print(e)
                        assert False, ('z3 returned unknown', res)

            if utils.args.use_z3_unsat_cores:
                assert core is not None
                ret_core: Optional[MySet[int]] = MySet(sorted(core))
            else:
                ret_core = None
            return (z3.unsat, ret_core)

    def clause_implied_by_transitions_from_frame(
            self,
            pre_frame: Frame,
            c: Expr,
            solver: Optional[Solver] = None,
            minimize: Optional[bool] = None
    ) -> Optional[Tuple[z3.ModelRef, DefinitionDecl]]:
        if solver is None:
            solver = self.solver
        return logic.check_two_state_implication_all_transitions(
            solver, pre_frame.summary(), c, minimize=minimize
        )

    def _simplify_summary(self, f: MySet[Expr]) -> None:
        l = []
        for c in reversed(f.l):
            f_minus_c = [x for x in f.l if x in f.s and x is not c]
            if c not in self.safeties and \
               logic.check_implication(self.solver, f_minus_c, [c], minimize=False) is None:
                f.s.remove(c)
            else:
                l.append(c)
        l.reverse()
        f.l = l

    def simplify(self) -> None:
        for i, f in enumerate(self.fs):
            self._simplify_summary(f._summary)

    def search(self) -> Frame:
        while True:
            self.establish_safety()
            self.simplify()
            if (f := self.get_inductive_frame()) is not None:
                utils.logger.always_print('frame is safe and inductive. done!')
                utils.logger.log_list(utils.MyLogger.ALWAYS_PRINT, [str(x) for x in f.summary()])
                return f
            self.new_frame()

    def store_frames(self, out_filename: str) -> None:
        s = self.solver
        try:
            self.solver = None  # type: ignore
            with open(out_filename, "wb") as f:
                pickle.dump(self, f)
        finally:
            self.solver = s

def load_frames(in_filename: str, s: Solver) -> Frames:
    with open(in_filename, "rb") as f:
        fs: Frames = pickle.load(f)
    fs.solver = s

    fs.always_assert_inductive_trace()

    return fs
