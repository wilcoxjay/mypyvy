import z3

import utils
from utils import MySet
import logic
from logic import Solver, Diagram, Trace, KEY_ONE, KEY_NEW, KEY_OLD, State
import syntax
from syntax import Expr, TrueExpr, DefinitionDecl
import pickle
from typing import List, Optional, Set, Tuple, Union, Sequence

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


class Frames:
    def __init__(self, solver: Solver) -> None:
        self.solver = solver
        self.fs: List[Frame] = []
        self.predicates: List[Expr] = []
        self.safeties = [inv.expr for inv in syntax.the_program.safeties()]
        self.backwards_reachable_states: List[State] = []

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
        print(f'starting frame {len(self.fs)}')
        self.fs.append(Frame(contents))
        self.push_forward_frames()

    def establish_safety(self) -> None:
        frame_no = len(self.fs) - 1

        while res := self._get_some_cex_to_safety():
            self.block(res, frame_no, [(None, res)])

    def _get_some_cex_to_safety(self) -> Optional[Diagram]:
        f = self.fs[-1]

        f_expr = syntax.And(*f.summary())
        for i, state in reversed(list(enumerate(self.backwards_reachable_states))):
            eval_res = state.eval(f_expr)
            assert isinstance(eval_res, bool)
            if eval_res:
                print(f'using state #{i}')
                return state.as_diagram()

        if (res := logic.check_implication(self.solver, f.summary(), self.safeties)) is None:
            return None

        z3m: z3.ModelRef = res
        mod = Trace.from_z3((KEY_ONE,), z3m)
        state = State(mod, 0)
        self.record_backwards_reachable_state(state)
        diag = state.as_diagram()
        return diag

    def record_backwards_reachable_state(self, state: State) -> None:
        print(f'discovered state #{len(self.backwards_reachable_states)}')
        print(state)
        self.backwards_reachable_states.append(state)

    def get_inductive_frame(self) -> Optional[Frame]:
        for i in range(len(self) - 1):
            if self.is_frame_inductive(i):
                return self[i + 1]
        return None

    def is_frame_inductive(self, i: int) -> bool:
        res = logic.check_implication(self.solver, self[i + 1].summary(), self[i].summary(), minimize=False)
        return res is None

    def push_conjunct(self, frame_no: int, c: Expr) -> None:
        f = self.fs[frame_no]
        if self.clause_implied_by_transitions_from_frame(f, c, minimize=False) is None:
            self[frame_no + 1].strengthen(c)

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
            diag: Diagram,
            j: int,
            trace: RelaxedTrace
    ) -> None:
        print(f'block({j})')
        if j == 0 or (j == 1 and self.valid_in_initial_frame(self.solver, diag) is not None):
            utils.logger.always_print('\n'.join(((t.name + ' ') if t is not None else '') +
                                                str(diag) for t, diag in trace))
            print('abstract counterexample: the system has no universal inductive invariant proving safety')
            if utils.args.checkpoint_out:
                self.store_frames(utils.args.checkpoint_out)
            raise AbstractCounterexample()

        while True:
            res, x = self.find_predecessor(self[j - 1], diag)
            if res == z3.unsat:
                assert x is None or isinstance(x, MySet)
                core: Optional[MySet[int]] = x
                self.augment_core_for_init(diag, core)
                break
            assert isinstance(x, tuple), (res, x)
            trans, cti = x
            pre_diag = cti.as_diagram(index=0)

            trace.append((trans, pre_diag))
            self.block(pre_diag, j - 1, trace)
            trace.pop()

        diag.minimize_from_core(core)

        def prev_frame_constraint(diag: Diagram) -> bool:
            pre_frame = self[j - 1].summary()
            return (
                logic.check_two_state_implication_all_transitions(
                    self.solver, pre_frame, syntax.Not(diag.to_ast()), minimize=False
                ) is None and
                diag.valid_in_init(self.solver, minimize=False)
            )

        diag.generalize(self.solver, prev_frame_constraint)
        self.add(syntax.Not(diag.to_ast()), j)

    def valid_in_initial_frame(self, s: Solver, diag: Diagram) -> Optional[z3.ModelRef]:
        return logic.check_implication(s, self.fs[0].summary(), [syntax.Not(diag.to_ast())])

    def augment_core_for_init(self, diag: Diagram, core: Optional[MySet[int]]) -> None:
        if core is None or not utils.args.use_z3_unsat_cores:
            return

        t = self.solver.get_translator((KEY_ONE,))

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
            pre_frame: Frame,
            diag: Diagram
    ) -> Tuple[z3.CheckSatResult, Union[Optional[MySet[int]], Tuple[DefinitionDecl, Trace]]]:
        prog = syntax.the_program
        solver = self.solver
        t = self.solver.get_translator((KEY_OLD, KEY_NEW))

        if utils.args.use_z3_unsat_cores:
            core: Optional[MySet[int]] = MySet()
        else:
            core = None

        with solver.new_frame(), solver.mark_assumptions_necessary():
            for f in pre_frame.summary():
                solver.add(t.translate_expr(f, index=0))
            solver.add(diag.to_z3(t, state_index=1))
            for ition in prog.transitions():
                with solver.new_frame():
                    solver.add(t.translate_transition(ition))
                    if (res := solver.check(diag.trackers)) == z3.sat:
                        m = Trace.from_z3((KEY_OLD, KEY_NEW), solver.model(diag.trackers))
                        self.record_backwards_reachable_state(State(m, 0))
                        return (z3.sat, (ition, m))
                    elif res == z3.unsat:
                        if utils.args.use_z3_unsat_cores:
                            assert core is not None
                            # carefully retrieve the unsat core before calling check again
                            uc = solver.unsat_core()
                            res = solver.check([diag.trackers[i] for i in core])
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
