import logging
import z3

import utils
from utils import MySet
import logic
from logic import Solver, Diagram, Trace, KEY_ONE, KEY_NEW, KEY_OLD, Blocked, CexFound
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
        self.push_cache: List[Set[Expr]] = []
        self.counter = 0
        self.predicates: List[Expr] = []
        self.state_count = 0
        self.safeties = [inv.expr for inv in syntax.the_program.safeties()]

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
        self.fs.append(Frame(contents))
        self.push_cache.append(set())
        self.push_forward_frames()

    def establish_safety(self) -> None:
        frame_no = len(self.fs) - 1

        while True:
            if (res := self._get_some_cex_to_safety()) is None:
                break

            self.block(res, frame_no, [(None, res)], True)

    def _get_some_cex_to_safety(self) -> Optional[Diagram]:
        f = self.fs[-1]

        if (res := logic.check_implication(self.solver, f.summary(), self.safeties)) is None:
            return None

        z3m: z3.ModelRef = res
        mod = Trace.from_z3((KEY_ONE,), z3m)
        diag = mod.as_diagram()
        return diag

    def get_inductive_frame(self) -> Optional[Frame]:
        for i in range(len(self) - 1):
            if self.is_frame_inductive(i):
                return self[i + 1]
        return None

    def is_frame_inductive(self, i: int) -> bool:
        res = logic.check_implication(self.solver, self[i + 1].summary(), self[i].summary(), minimize=False)
        return res is None

    def push_conjunct(self, frame_no: int, c: Expr,
                      frame_old_count: Optional[int] = None) -> None:
        is_safety = c in self.safeties

        f = self.fs[frame_no]
        while True:
            res = self.clause_implied_by_transitions_from_frame(
                f,
                c,
                minimize=is_safety or utils.args.block_may_cexs
            )
            if res is None:
                self[frame_no + 1].strengthen(c)
                break

            m, t = res
            mod = Trace.from_z3((KEY_OLD, KEY_NEW), m)
            diag = mod.as_diagram(i=0)

            if is_safety:
                self.block(diag, frame_no, [(None, c), (t, diag)], safety_goal=True)
            else:
                if utils.args.block_may_cexs:
                    ans = self.block(diag, frame_no, [(None, c), (t, diag)], safety_goal=False)
                    if isinstance(ans, CexFound):
                        break
                else:
                    break

    def push_forward_frames(self) -> None:
        for i, f in enumerate(self.fs[:-1]):
            if i == 0 and not utils.args.push_frame_zero:
                continue
            self.push_frame(i, f)

    def always_assert_inductive_trace(self) -> None:
        for i, f in enumerate(self.fs[:-1]):
            for c in self.fs[i + 1].summary():
                res = self.clause_implied_by_transitions_from_frame(f, c, Solver())
                assert res is None, ("Non inductive trace:\n\t%s\n\t%s" % (c, f))

    def push_frame(self, i: int, f: Frame) -> None:
        frame_old_count = self.counter
        conjuncts = f._summary
        j = 0
        while j < len(conjuncts):
            c = conjuncts.l[j]
            if c in self.fs[i + 1]._summary or c in self.push_cache[i]:
                return
            self.push_conjunct(i, c, frame_old_count)
            self.push_cache[i].add(c)
            j += 1

    # Block the diagram in the given frame.
    # If safety_goal is True, the only possible outcomes are returning Blocked() on success
    # or throwing an exception describing an abstract counterexample on failure.
    # If safety_goal is False, then no abstract counterexample is ever reported to user,
    # instead, CexFound() is returned to indicate the diagram could not be blocked.
    def block(
            self,
            diag: Diagram,
            j: int,
            trace: Optional[RelaxedTrace] = None,
            safety_goal: bool = True
    ) -> Union[Blocked, CexFound]:
        if trace is None:
            trace = []
        if j == 0 or (j == 1 and self.valid_in_initial_frame(self.solver, diag) is not None):
            if safety_goal:
                utils.logger.always_print('\n'.join(((t.name + ' ') if t is not None else '') +
                                                    str(diag) for t, diag in trace))
                print('abstract counterexample: the system has no universal inductive invariant proving safety')
                if utils.args.checkpoint_out:
                    self.store_frames(utils.args.checkpoint_out)
                raise AbstractCounterexample()
            else:
                return CexFound()

        while True:
            res, x = self.find_predecessor(self[j - 1], diag)
            if res == z3.unsat:
                assert x is None or isinstance(x, MySet)
                core: Optional[MySet[int]] = x
                self.augment_core_for_init(diag, core)
                break
            assert isinstance(x, tuple), (res, x)
            trans, pre_diag = x

            trace.append((trans, pre_diag))
            ans = self.block(pre_diag, j - 1, trace, safety_goal)
            if not isinstance(ans, Blocked):
                return ans
            trace.pop()

        diag.minimize_from_core(core)
        diag.generalize(self.solver, self[j - 1].summary())

        self.add(syntax.Not(diag.to_ast()), j)

        return Blocked()

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
        self.counter += 1

        if depth is None:
            depth = len(self)

        for i in range(depth + 1):
            self[i].strengthen(e)

    def find_predecessor(
            self,
            pre_frame: Frame,
            diag: Diagram
    ) -> Tuple[z3.CheckSatResult, Union[Optional[MySet[int]], Tuple[DefinitionDecl, Diagram]]]:
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
                        return (z3.sat, (ition, m.as_diagram(i=0)))
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
