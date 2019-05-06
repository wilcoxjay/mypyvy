from collections import OrderedDict
from syntax import AutomatonDecl, PhaseDecl, PhaseTransitionDecl, Expr, TrueExpr, InvariantDecl
from typing import List, Optional, Dict, Sequence
import utils
from utils import MySet

class Phase(object):
    def __init__(self, phase_decl: PhaseDecl) -> None:
        self.phase_decl = phase_decl
        self.safety = list(phase_decl.safeties())
        self.sketch_invs = list(phase_decl.sketch_invs())

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

    def prog_transition_name(self) -> str:
        return self._transition_decl.transition

    def precond(self) -> Optional[Expr]:
        return self._transition_decl.precond

    def transition_decl(self) -> PhaseTransitionDecl:
        return self._transition_decl

    def pp(self) -> str:
        return '%s assume %s' % (self._transition_decl.transition, self._transition_decl.precond)

    def __repr__(self) -> str:
        return 'PhaseTransition(src=%s, target=%s, transition_decl=%s)' % (
            self._src.name(),
            self._target.name(),
            self._transition_decl
        )

    def __str__(self) -> str:
        return str(self.transition_decl())


class PhaseAutomaton(object):
    def __init__(self, automaton_decl: AutomatonDecl) -> None:
        self.automaton_decl = automaton_decl

        self._phases: Dict[str, Phase] = OrderedDict()
        for p in self.automaton_decl.phases():
            self._phases[p.name] = Phase(p)

        self._transitions = [PhaseTransition(self._phases[p.name],
                                             self._phases[(delta.target if delta.target is not None else p.name)],
                                             delta)
                                for p in self.automaton_decl.phases()
                                for delta in p.transitions()]

        init_decl = automaton_decl.the_init()
        assert init_decl is not None
        self._init_phase = self._phases[init_decl.phase]

        self.nontrivial = len(self._phases) > 1

    def phases(self) -> Sequence[Phase]:
        return list(self._phases.values())

    def phase_by_name(self, name: str) -> Phase:
        return self._phases[name]

    def init_phase(self) -> Phase:
        return self._init_phase

    def predecessors(self, trg: Phase) -> List[Phase]:
        return [t.src() for t in self._transitions if t.target() == trg]

    def transitions_between(self, src: Phase, target: Phase) -> List[PhaseTransition]:
        return list(filter(lambda t: (t.src() == src) & (t.target() == target), self._transitions))

    def transitions_to_grouped_by_src(self, target: Phase) -> Dict[Phase, Sequence[PhaseTransition]]:
        return {p: self.transitions_between(p, target) for p in self.predecessors(target)}

    def transitions_from(self, p: Phase) -> Sequence[PhaseTransition]:
        return [t for t in self._transitions if t.src() == p ]


class Frame(object):
    def __init__(self, phases: Sequence[Phase], summaries: Optional[Dict[Phase, Sequence[Expr]]]=None) -> None:
        self._summary_by_pred: Dict[Phase, MySet[Expr]] = OrderedDict()
        if summaries is None:
            summaries = {}
        for phase in phases:
            self._summary_by_pred[phase] = MySet(summaries.get(phase, [TrueExpr]))

    def phases(self) -> Sequence[Phase]:
        return list(self._summary_by_pred.keys())

    def summary_of(self, phase: Phase) -> MySet[Expr]:
        return self._summary_by_pred[phase]

    def strengthen(self, phase: Phase, conjunct: Expr) -> None:
        self._summary_by_pred[phase].add(conjunct)

    def __str__(self) -> str:
        return str({p.name(): [str(x) for x in summary] for (p, summary) in self._summary_by_pred.items()})

def phase_safety(p: Phase) -> Sequence[InvariantDecl]:
    if utils.args.sketch:
        return p.safety + p.sketch_invs
    return p.safety
