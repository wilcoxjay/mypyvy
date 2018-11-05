from syntax import AutomatonDecl, PhaseDecl, PhaseTransitionDecl, Expr, TrueExpr
from typing import List, Any, Optional, Callable, Set, Tuple, Union, Iterable, \
    Dict, TypeVar, Sequence, overload, Generic, Iterator, cast
from utils import MySet

class Phase(object):
    def __init__(self, phase_decl: PhaseDecl) -> None:
        self.phase_decl = phase_decl

    def name(self) -> str:
        return self.phase_decl.name

    def __repr__(self) -> str:
        return 'Phase(phase_decl=%s)' % (
            self.phase_decl,
        )

    def __str__(self) -> str:
        return str(self.phase_decl)

class PhaseTransition(object):
    def __init__(self, src: Phase, target: Phase, transition_decl: PhaseTransitionDecl) -> None:
        self._src: Phase = src
        self._target: Phase = target
        self._transition_decl = transition_decl

    def src(self) -> Phase:
        return self._src

    def target(self) -> Phase:
        return self._target

    def transition_decl(self):
        return self._transition_decl

    def __repr__(self) -> str:
        return 'PhaseTransition(src=%s, target=%s, transition_decl=%s)' % (
            self._src,
            self._target,
            self._transition_decl
        )

    def __str__(self) -> str:
        return str(self.transition_decl)


class PhaseAutomaton(object):
    def __init__(self, automaton_decl: AutomatonDecl) -> None:
        self.automaton_decl = automaton_decl

        self._phases = {p.name : Phase(p) for p in self.automaton_decl.phases()}

        self._transitions = [PhaseTransition(self._phases[p.name],
                                             self._phases[(delta.target if delta.target is not None else p.name)],
                                             delta)
                                for p in self.automaton_decl.phases()
                                for delta in p.transitions()]

        self._init_phase = self._phases[automaton_decl.the_init().phase]

    def phases(self) -> Iterable[Phase]:
        return self._phases.values()

    def phase_by_name(self, name: str) -> Phase:
        return self._phases[name]

    def init_phase(self) -> Phase:
        return self._init_phase

    def predecessors(self, trg: Phase) -> List[Phase]:
        return [t.src() for t in self._transitions if t.target() == trg]

    def transitions_between(self, src: Phase, target: Phase) -> List[Phase]:
        return filter(lambda t: t.src() == src & t.target() == target, self._transitions)

    def transitions_to_grouped_by_src(self, target: Phase) -> Dict[Phase, List[PhaseTransition]]:
        return {p: self.transitions_between(p, target) for p in self.transitions_between()}


class Frame(object):
    def __init__(self, phases: Sequence[Phase], summaries: Optional[Dict[Phase, Sequence[Expr]]]=None):
        self._summary_by_pred: Dict[Phase, MySet[Expr]] = {}
        if summaries is None:
            summaries = {}
        for phase in phases:
            self._summary_by_pred[phase] = MySet(summaries.get(phase, [TrueExpr]))

    def summary_of(self, phase: Phase) -> MySet[Expr]:
        return self._summary_by_pred[phase]

    def strengthen(self, phase: Phase, conjunct: Expr) -> None:
        self._summary_by_pred[phase].add(conjunct)