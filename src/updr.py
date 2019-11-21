from datetime import datetime
import itertools
import logging
import z3

import utils
from utils import MySet
import logic
from logic import Solver, Diagram, Trace, KEY_ONE, KEY_NEW, KEY_OLD, Blocked, CexFound
import phases
import syntax
from syntax import Expr, AutomatonDecl
import pickle
from typing import List, Optional, Set, Tuple, Union, Dict, Sequence

from phases import PhaseAutomaton, Phase, Frame, PhaseTransition

RelaxedTrace = List[Tuple[Optional[PhaseTransition], Union[Diagram, Expr]]]

class AbstractCounterexample(Exception):
    pass

def equiv_expr(solver: Solver, e1: Expr, e2: Expr) -> bool:
    return (logic.check_implication(solver, [e1], [e2], minimize=False) is None and
            logic.check_implication(solver, [e2], [e1], minimize=False) is None)

class Frames(object):
    @utils.log_start_end_xml(utils.logger, logging.DEBUG, 'Frames.__init__')
    def __init__(self, solver: Solver) -> None:
        self.solver = solver
        prog = syntax.the_program

        if utils.args.automaton:
            automaton = prog.the_automaton()
            if automaton is None:
                utils.print_error_and_exit(None, 'updr --automaton requires the file to '
                                           'declare an automaton')
        else:
            the_phase = 'the_phase'
            pcs: List[syntax.PhaseComponent] = []
            for t in prog.transitions():
                pcs.append(syntax.PhaseTransitionDecl(None, t.name, None, the_phase))
            for inv in prog.safeties():
                pcs.append(inv)

            automaton = AutomatonDecl(None, [syntax.InitPhaseDecl(None, the_phase),
                                             syntax.PhaseDecl(None, the_phase, pcs)])

            automaton.resolve(prog.scope)

        self.automaton = PhaseAutomaton(automaton)
        self.fs: List[Frame] = []
        self.push_cache: List[Dict[Phase, Set[Expr]]] = []
        self.counter = 0
        self.predicates: List[Expr] = []
        self.state_count = 0
        self.human_invariant = tuple(itertools.chain(*(syntax.as_clauses(inv.expr) for inv in prog.invs() if not inv.is_safety))) # convert to CNF

        self._first_frame()

    def __getitem__(self, i: int) -> Frame:
        return self.fs[i]

    def __setitem__(self, i: int, e: Frame) -> None:
        assert e is self.fs[i]

    def __len__(self) -> int:
        return len(self.fs)

    def _first_frame(self) -> None:
        init_conjuncts = [init.expr for init in syntax.the_program.inits()]
        self.new_frame({p: init_conjuncts if p == self.automaton.init_phase()
                                          else [syntax.FalseExpr]
                         for p in self.automaton.phases()})

    @utils.log_start_end_xml(utils.logger, logging.DEBUG)
    def new_frame(self, contents: Optional[Dict[Phase, Sequence[Expr]]] = None) -> None:
        if contents is None:
            contents = {}
        utils.logger.debug("new frame! %s" % len(self.fs))
        self.fs.append(Frame(self.automaton.phases(), contents))
        self.push_cache.append({p: set() for p in self.automaton.phases()})

        self.push_forward_frames()

        with utils.LogTag(utils.logger, 'current-frames-after-push', lvl=logging.DEBUG):
            self.print_frames(lvl=logging.DEBUG)

    @utils.log_start_end_xml(utils.logger)
    def establish_safety(self) -> None:
        self.debug_assert_inductive_trace()

        frame_no = len(self.fs) - 1

        while True:
            with utils.LogTag(utils.logger, 'establish-safety-attempt'):
                res = self._get_some_cex_to_safety()

                if res is None:
                    break

                (violating, diag) = res
                self.block(diag, frame_no, violating, [(None, diag)], True)

        self.debug_assert_inductive_trace()

    def _get_some_cex_to_safety(self) -> Optional[Tuple[Phase, Diagram]]:
        f = self.fs[-1]

        def safety_property_checker(p: Phase) -> Optional[Tuple[Phase, Diagram]]:
            res = logic.check_implication(self.solver, f.summary_of(p),
                                          (inv.expr for inv in phases.phase_safety(p)))

            if res is None:
                utils.logger.debug("Frontier frame phase %s implies safety, summary is %s" %
                                   (p.name(), f.summary_of(p)))
                return None

            utils.logger.debug("Frontier frame phase %s cex to safety" % p.name())
            z3m: z3.ModelRef = res
            mod = Trace.from_z3([KEY_ONE], z3m)
            self.record_state(mod)
            diag = mod.as_diagram()
            return (p, diag)

        def edge_covering_checker(p: Phase) -> Optional[Tuple[Phase, Diagram]]:
            t = self.solver.get_translator(KEY_NEW, KEY_OLD)
            f = self.fs[-1]
            prog = syntax.the_program

            with self.solver:
                for c in f.summary_of(p):
                    self.solver.add(t.translate_expr(c, old=True))

                transitions_from_phase = self.automaton.transitions_from(p)

                for trans in prog.transitions():
                    edges_from_phase_matching_prog_trans = [
                        t for t in transitions_from_phase
                        if t.prog_transition_name() == trans.name
                    ]
                    if any(delta.precond is None
                           for delta in edges_from_phase_matching_prog_trans):
                        utils.logger.debug('transition %s is covered trivially by %s' %
                                           (trans.name, p.name()))
                        continue

                    utils.logger.debug('checking transition %s is covered by %s' %
                                       (trans.name, p.name()))

                    with self.solver:
                        self.solver.add(t.translate_transition(trans))
                        preconds = (
                            z3.Not(t.translate_precond_of_transition(delta.precond(), trans))
                            for delta in edges_from_phase_matching_prog_trans
                        )
                        self.solver.add(z3.And(*preconds))

                        if self.solver.check() != z3.unsat:
                            utils.logger.debug('phase %s cex to edge covering of transition %s' %
                                               (p.name(), trans.name))
                            z3m: z3.ModelRef = self.solver.model()
                            mod = Trace.from_z3([KEY_OLD, KEY_NEW], z3m)
                            self.record_state(mod)
                            diag = mod.as_diagram(i=0)
                            return (p, diag)

                        utils.logger.debug('transition %s is covered non-trivially by %s' %
                                           (trans.name, p.name()))
                        continue

                utils.logger.debug('all edges covered from phase %s' % p.name())
                return None

        safety_checkers = [safety_property_checker, edge_covering_checker]
        for p in self.automaton.phases():
            for checker in safety_checkers:
                sres = checker(p)
                if sres is not None:
                    return sres
        return None

    @utils.log_start_end_xml(utils.logger, logging.DEBUG)
    def get_inductive_frame(self) -> Optional[Frame]:
        for i in range(len(self) - 1):
            if self.is_frame_inductive(i):
                return self[i + 1]
        return None

    def is_frame_inductive(self, i: int) -> bool:
        for p in self.automaton.phases():
            if logic.check_implication(self.solver,
                                       self[i + 1].summary_of(p),
                                       self[i].summary_of(p),
                                       minimize=False) is not None:
                return False
        return True

    def push_conjunct(self, frame_no: int, c: Expr, p: Phase,
                      frame_old_count: Optional[int] = None) -> None:
        is_safety = c in phases.phase_safety(p)

        f = self.fs[frame_no]
        while True:
            with utils.LogTag(utils.logger, 'pushing-conjunct-attempt', lvl=logging.DEBUG,
                              frame=str(frame_no), conj=str(c)):
                utils.logger.debug('frame %s phase %s attempting to push %s' %
                                   (frame_no, p.name(), c))

                res = self.clause_implied_by_transitions_from_frame(f, p, c, minimize=is_safety or utils.args.block_may_cexs)
                if res is None:
                    utils.logger.debug('frame %s phase %s managed to push %s' %
                                       (frame_no, p.name(), c))

                    if utils.args.smoke_test and utils.logger.isEnabledFor(logging.DEBUG):
                        utils.logger.debug('smoke testing...')
                        # TODO: phases
                        logic.check_bmc(self.solver, c, frame_no + 1)

                    # assert self.clause_implied_by_transitions_from_frame(f, p, c) is None
                    self[frame_no + 1].strengthen(p, c)
                    self.debug_assert_inductive_trace()
                    break

                pre_phase, (m, t) = res
                mod = Trace.from_z3([KEY_OLD, KEY_NEW], m)
                self.record_state(mod)
                diag = mod.as_diagram(i=0)

                if utils.logger.isEnabledFor(logging.DEBUG):
                    utils.logger.debug('frame %s failed to immediately push %s due to '
                                       'transition %s' % (frame_no, c, t.pp()))
                    # utils.logger.debug(str(mod))
                if is_safety:
                    utils.logger.debug('note: current clause is safety condition')
                    self.block(diag, frame_no, pre_phase, [(None, c), (t, diag)], safety_goal=True)
                else:
                    if utils.args.block_may_cexs:
                        ans = self.block(diag, frame_no, pre_phase, [(None, c), (t, diag)],
                                         safety_goal=False)
                        if isinstance(ans, CexFound):
                            break
                    else:
                        break

    @utils.log_start_end_xml(utils.logger, logging.DEBUG)
    def push_forward_frames(self) -> None:
        self.debug_assert_inductive_trace()
        for i, f in enumerate(self.fs[:-1]):
            if ((utils.args.push_frame_zero == 'if_trivial' and self.automaton.nontrivial) or
                    (utils.args.push_frame_zero == 'never')) and i == 0:
                continue
            with utils.LogTag(utils.logger, 'pushing-frame', lvl=logging.DEBUG, i=str(i)):
                for p in self.automaton.phases():
                    utils.logger.debug('pushing in frame %d phase %s' % (i, p.name()))
                    self.push_phase_from_pred(i, f, p)
                    # self.debug_assert_inductive_trace()

        self.debug_assert_inductive_trace()

    def debug_assert_inductive_trace(self) -> None:
        if not utils.args.assert_inductive_trace:
            return

        self.debug_assert_inductive_trace()

    def always_assert_inductive_trace(self) -> None:
        for i, f in enumerate(self.fs[:-1]):
            with utils.LogTag(utils.logger, 'inductive-trace-assert', lvl=logging.DEBUG, i=str(i)):
                for p in self.automaton.phases():
                    for c in self.fs[i + 1].summary_of(p):
                        res = self.clause_implied_by_transitions_from_frame(f, p, c, Solver())
                        assert res is None, ("Non inductive trace:\n\t%s\n\t%s\n\t%s" %
                                             (p.name(), c, f))

    def push_phase_from_pred(self, i: int, f: Frame, p: Phase) -> None:
        frame_old_count = self.counter

        def process_conjunct(c: Expr) -> None:
            if c in self.fs[i + 1].summary_of(p) or c in self.push_cache[i][p]:
                return

            with utils.LogTag(utils.logger, 'pushing-conjunct', lvl=logging.DEBUG,
                              frame=str(i), conj=str(c)):
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
    @utils.log_start_end_xml(utils.logger, lvl=logging.DEBUG)
    def block(
            self,
            diag: Diagram,
            j: int,
            p: Phase,
            trace: Optional[RelaxedTrace] = None,
            safety_goal: bool = True
    ) -> Union[Blocked, CexFound]:
        if trace is None:
            trace = []
        if j == 0 or (j == 1 and self.valid_in_initial_frame(self.solver, p, diag) is not None):
            if safety_goal:
                utils.logger.always_print('\n'.join(((t.pp() + ' ') if t is not None else '') +
                                                    str(diag) for t, diag in trace))
                print('abstract counterexample: the system has no universal inductive invariant proving safety')
                # TODO: placeholder for analyzing relaxed trace
                # import relaxed_traces
                # print(relaxed_traces.diagram_trace_to_explicitly_relaxed_trace(trace, phases.phase_safety(p)))
                if utils.args.checkpoint_out:
                    self.store_frames(utils.args.checkpoint_out)
                raise AbstractCounterexample()
            else:
                if utils.logger.isEnabledFor(logging.DEBUG):
                    utils.logger.debug('failed to block diagram')
                return CexFound()

        while True:
            with utils.LogTag(utils.logger, 'block-attempt'):
                if utils.logger.isEnabledFor(logging.DEBUG):
                    utils.logger.debug('blocking diagram in frame %s' % j)
                    utils.logger.debug(str(diag))

                    self.print_frame(j - 1, lvl=logging.DEBUG)
                res, x = self.find_predecessor(self[j - 1], p, diag)
                if res == z3.unsat:
                    utils.logger.debug('no predecessor: blocked!')
                    assert x is None or isinstance(x, MySet)
                    core: Optional[MySet[int]] = x
                    self.augment_core_for_init(p, diag, core)
                    break
                assert isinstance(x, tuple), (res, x)
                trans, (pre_phase, pre_diag) = x

                trace.append((trans, pre_diag))
                ans = self.block(pre_diag, j - 1, pre_phase, trace, safety_goal)
                if not isinstance(ans, Blocked):
                    return ans
                trace.pop()

        if utils.logger.isEnabledFor(logging.DEBUG) and core is not None:
            utils.logger.debug('core %s' % core)
            utils.logger.debug('unminimized diag\n%s' % diag)

        diag.minimize_from_core(core)
        diag.generalize(self.solver,
                        self[j - 1],
                        self.automaton.transitions_to_grouped_by_src(p),
                        p == self.automaton.init_phase(),
                        j)

        e = syntax.Not(diag.to_ast())

        if utils.logger.isEnabledFor(logging.DEBUG):
            utils.logger.debug('adding new clause to frames 0 through %d phase %s' % (j, p.name()))
        if utils.logger.isEnabledFor(logging.INFO):
            utils.logger.info("[%d] %s" % (j, str(e)))

        self.add(p, e, j)
        utils.logger.debug("Done blocking")

        return Blocked()

    def valid_in_initial_frame(self, s: Solver, p: Phase, diag: Diagram) -> Optional[z3.ModelRef]:
        return logic.check_implication(s, self.fs[0].summary_of(p), [syntax.Not(diag.to_ast())])

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
            # if utils.logger.isEnabledFor(logging.DEBUG):
            #     utils.logger.debug('uc')
            #     utils.logger.debug(str(sorted(uc, key=lambda y: y.decl().name())))

            #     utils.logger.debug('assertions')
            #     utils.logger.debug(str(self.solver.assertions()))

            res = self.solver.check([diag.trackers[i] for i in core])
            if res == z3.unsat:
                utils.logger.debug('augment_core_for_init: existing core sufficient')
                return

            for x in sorted(uc, key=lambda y: y.decl().name()):
                assert isinstance(x, z3.ExprRef)
                core.add(int(x.decl().name()[1:]))
            if utils.logger.isEnabledFor(logging.DEBUG):
                utils.logger.debug('augment_core_for_init: new core')
                utils.logger.debug(str(sorted(core)))

    def record_state(self, m: Trace) -> None:
        self.state_count += 1
        utils.logger.info(f'learned state {self.state_count}')
        utils.logger.debug(str(m))

    def record_predicate(self, e: Expr) -> None:
        for x in self.predicates:
            if x == e or equiv_expr(self.solver, x, e):
                break
        else:
            self.predicates.append(e)
            for x in self.human_invariant:
                if equiv_expr(self.solver, x, e):
                    msg = '(which is a clause of the human invariant)'
                    break
            else:
                msg = ''

            utils.logger.info(f'learned new predicate, now have {len(self.predicates)} {e} {msg}')

    def add(self, p: Phase, e: Expr, depth: Optional[int] = None) -> None:
        self.counter += 1

        self.record_predicate(e)

        if depth is None:
            depth = len(self)

        if utils.args.smoke_test and utils.logger.isEnabledFor(logging.DEBUG):
            utils.logger.debug('smoke testing at depth %s...' % (depth,))
            logic.check_bmc(self.solver, e, depth)

        self.debug_assert_inductive_trace()
        for i in range(depth + 1):
            self[i].strengthen(p, e)
            utils.logger.debug("%d %s %s" % (i, p.name(), e))
            self.debug_assert_inductive_trace()
        self.debug_assert_inductive_trace()

    @utils.log_start_end_xml(utils.logger, lvl=logging.DEBUG)
    def find_predecessor(
            self,
            pre_frame: Frame,
            current_phase: Phase,
            diag: Diagram
    ) -> Tuple[z3.CheckSatResult,
               Union[Optional[MySet[int]], Tuple[PhaseTransition, Tuple[Phase, Diagram]]]]:
        t = self.solver.get_translator(KEY_NEW, KEY_OLD)

        if utils.args.use_z3_unsat_cores:
            core: Optional[MySet[int]] = MySet()
        else:
            core = None

        with self.solver:
            with self.solver.mark_assumptions_necessary():
                self.solver.add(diag.to_z3(t))

                transitions_into = self.automaton.transitions_to_grouped_by_src(current_phase)
                for src in self._predecessor_precedence(current_phase,
                                                        list(transitions_into.keys())):
                    transitions = transitions_into[src]
                    assert transitions
                    utils.logger.debug("check predecessor of %s from %s by %s" %
                                       (current_phase.name(), src.name(), transitions))
                    (sat_res, pre_diag) = self.find_predecessor_from_src_phase(
                        t, pre_frame, src, transitions, diag, core
                    )
                    if sat_res == z3.unsat:
                        continue
                    return (sat_res, pre_diag)

                if utils.args.use_z3_unsat_cores:
                    assert core is not None
                    ret_core: Optional[MySet[int]] = MySet(sorted(core))
                else:
                    ret_core = None

                return (z3.unsat, ret_core)

    def _predecessor_precedence(
            self,
            dst_phase: Phase,
            pre_phases: Sequence[Phase]
    ) -> Sequence[Phase]:
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

        prog = syntax.the_program
        solver = self.solver
        with solver:

            for f in pre_frame.summary_of(src_phase):
                solver.add(t.translate_expr(f, old=True))

            for phase_transition in transitions:
                delta = phase_transition.transition_decl()
                trans = prog.scope.get_definition(delta.transition)
                assert trans is not None
                precond = delta.precond

                with utils.LogTag(utils.logger, 'find-pred', transition=delta.transition, weight=str(phase_transition.avg_time_traversing())):
                    with solver:
                        solver.add(t.translate_transition(trans, precond=precond))
                        before_check = datetime.now()
                        res = solver.check(diag.trackers)
                        phase_transition.time_spent_traversing += (datetime.now() - before_check).total_seconds()
                        phase_transition.count_traversed += 1

                        if res != z3.unsat:
                            utils.logger.debug('found predecessor via %s' % trans.name)
                            m = Trace.from_z3([KEY_OLD, KEY_NEW], solver.model(diag.trackers))
                            # if utils.logger.isEnabledFor(logging.DEBUG):
                            #     utils.logger.debug(str(m))
                            self.record_state(m)
                            return (res, (phase_transition, (src_phase, m.as_diagram(i=0))))
                        elif utils.args.use_z3_unsat_cores:
                            assert core is not None
                            uc = solver.unsat_core()
                            # if utils.logger.isEnabledFor(logging.DEBUG):
                            #     utils.logger.debug('uc')
                            #     utils.logger.debug(str(sorted(uc, key=lambda y: y.decl().name())))
                            #     utils.logger.debug('assertions')
                            #     utils.logger.debug(str(solver.assertions()))

                            res = solver.check([diag.trackers[i] for i in core])
                            if res == z3.unsat:
                                utils.logger.debug('but existing core sufficient, skipping')
                                continue

                            for x in sorted(uc, key=lambda y: y.decl().name()):
                                assert isinstance(x, z3.ExprRef)
                                core.add(int(x.decl().name()[1:]))
                            if utils.logger.isEnabledFor(logging.DEBUG):
                                utils.logger.debug('new core')
                                utils.logger.debug(str(sorted(core)))

            return (z3.unsat, None)

    def clause_implied_by_transitions_from_frame(
            self,
            pre_frame: Frame,
            current_phase: Phase,
            c: Expr,
            solver: Optional[Solver] = None,
            minimize: Optional[bool] = None
    ) -> Optional[Tuple[Phase, Tuple[z3.ModelRef, PhaseTransition]]]:
        if solver is None:
            solver = self.solver
        automaton = self.automaton
        for src, transitions in automaton.transitions_to_grouped_by_src(current_phase).items():
            utils.logger.debug("check transition from %s by %s" %
                               (src.name(), str(list(transitions))))

            ans = logic.check_two_state_implication_along_transitions(
                solver, pre_frame.summary_of(src), transitions, c, minimize=minimize
            )
            if ans is not None:
                return (src, ans)

        return None

    def _simplify_summary(self, f: MySet[Expr], p: Phase) -> None:
        l = []
        for c in reversed(f.l):
            f_minus_c = [x for x in f.l if x in f.s and x is not c]
            if c not in phases.phase_safety(p) and \
               logic.check_implication(self.solver, f_minus_c, [c], minimize=False) is None:
                utils.logger.debug('removed %s' % c)
                f.s.remove(c)
            else:
                l.append(c)
        l.reverse()
        f.l = l

    @utils.log_start_end_xml(utils.logger)
    def simplify(self) -> None:
        for i, f in enumerate(self.fs):
            for p in self.automaton.phases():
                with utils.LogTag(utils.logger, 'simplify', frame=str(i)):
                    utils.logger.debug('simplifying frame %d, pred %s' % (i, p.name()))
                    self._simplify_summary(f.summary_of(p), p)

    def print_frame(self, i: int, lvl: int = logging.INFO) -> None:
        f = self.fs[i]
        with utils.LogTag(utils.logger, 'frame', i=str(i)):
            for p in self.automaton.phases():
                utils.logger.log_list(lvl,
                                      ['frame %d of %s is' % (i, p.name())] +
                                      [str(x) for x in f.summary_of(p)])

    def print_frames(self, lvl: int = logging.INFO) -> None:
        for i, _ in enumerate(self.fs):
            self.print_frame(i, lvl=lvl)

    def search(self) -> Frame:
        while True:
            self.establish_safety()
            with utils.LogTag(utils.logger, 'current-frames-after-safety', lvl=logging.DEBUG):
                self.print_frames(lvl=logging.DEBUG)

            self.simplify()
            with utils.LogTag(utils.logger, 'current-frames-after-simplify', lvl=logging.DEBUG):
                self.print_frames(lvl=logging.DEBUG)

            n = len(self) - 1
            with utils.LogTag(utils.logger, 'check-frame', lvl=logging.INFO, n=str(n)):
                with utils.LogTag(utils.logger, 'current-frames', lvl=logging.INFO):
                    self.print_frames()

                utils.logger.info('considering frame %s' % (len(self) - 1,))

                f = self.get_inductive_frame()
                if f is not None:
                    utils.logger.always_print('frame is safe and inductive. done!')
                    for p in self.automaton.phases():
                        utils.logger.log_list(utils.MyLogger.ALWAYS_PRINT,
                                              ['summary of %s: ' % p.name()] +
                                              [str(x) for x in f.summary_of(p)])
                    return f

                utils.logger.info('frame is safe but not inductive. starting new frame')
            self.new_frame()

    def store_frames(self, out_filename: str) -> None:
        s = self.solver
        try:
            self.solver = None # type: ignore
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
