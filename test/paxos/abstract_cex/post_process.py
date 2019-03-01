from __future__ import annotations
from typing import List, Iterable, Tuple, Dict, Optional, Set
from dataclasses import dataclass
from collections import defaultdict

@dataclass
class State(object):
    universe: List[str]
    conjuncts: List[str]

    def sort_for_elt(self, elt: str) -> Optional[str]:
        def base_name(s: str) -> str:
            return s.strip('0123456789')
        sorts = set(base_name(s) for s in self.universe)
        candidate = base_name(elt)
        if candidate in sorts:
            return candidate
        else:
            return None

    @staticmethod
    def from_lines(lines: List[str]) -> State:
        universe = lines[0][len('exists '):].strip('.').split(', ')
        conjuncts = lines[1:]
        return State(universe, conjuncts)

@dataclass
class Trace(object):
    states: List[State]
    actions: List[str]

    def __post_init__(self) -> None:
        assert len(self.states) == len(self.actions) + 1


def parse_trace(itr: Iterable[str]) -> Trace:
    states: List[List[str]] = []
    actions: List[str] = []
    started = False
    for line in itr:
        if not started and line.startswith('exists'):
            started = True

        if started:
            if line.startswith('Traceback'):
                break
            if not line.startswith(' '):
                states.append([])
                delim = ' assume None '
                if delim in line:
                    l = line.split(delim)
                    assert len(l) == 2
                    action, line = l
                    actions.append(action)

            states[-1].append(line.strip('\n &'))

    states.reverse()
    actions.reverse()

    return Trace([State.from_lines(state) for state in states], actions)

def filter_negative_facts(state: State) -> None:
    state.conjuncts = [line for line in state.conjuncts if '!' not in line]

def remove_equalities(state: State) -> List[Tuple[str, str]]:
    new_conjuncts = []
    eqs = []
    for c in state.conjuncts:
        if '=' in c:
            l = c.split(' = ')
            assert len(l) == 2
            a, b = l
            eqs.append((a, b))
        else:
            new_conjuncts.append(c)

    state.conjuncts = new_conjuncts

    return eqs

def substitute_constants(state: State) -> None:
    eqs = remove_equalities(state)

    for const, var in eqs:
        state.conjuncts = [c.replace(var, const) for c in state.conjuncts]
        state.universe.remove(var)

def find_relational_facts(rel: str, conjuncts: List[str]) -> Tuple[List[str], List[str], List[str]]:
    pre = []
    relevant = []
    post = []
    for line in conjuncts:
        if line.startswith(rel + '('):
            relevant.append(line)
        elif len(relevant) == 0:
            pre.append(line)
        else:
            post.append(line)
    return pre, relevant, post


def rename(s: str, renaming: Dict[str, str]) -> str:
    i = 0
    ans = []
    while i < len(s):
        for k,v in renaming.items():
            if s.startswith(k, i):
                ans.append(v)
                i += len(k)
                break
        else:
            ans.append(s[i])
            i += 1
    return ''.join(ans)

def rename_state(state: State, renaming: Dict[str, str]) -> None:
    state.universe = [rename(elt, renaming) for elt in state.universe]
    state.conjuncts = [rename(c, renaming) for c in state.conjuncts]

def filter_total_order_facts(rel: str, state: State) -> None:
    pre, relevant, post = find_relational_facts(rel, state.conjuncts)

    d: Dict[str,int] = defaultdict(int)
    for fact in relevant:
        fact = fact[len(rel)+len('('):]
        l = fact.split(',')
        assert len(l) == 2
        elt, _ = l
        d[elt] += 1

    n = len(d)
    elts = ['' for i in range(n)]
    for k, count in d.items():
        assert 1 <= count and count <= n
        assert elts[count-1] == ''
        elts[count-1] = k

    elts.reverse()

    new_facts = []
    for a, b in zip(elts, elts[1:]):
        new_facts.append('%s(%s, %s)' % (rel, a, b))

    state.conjuncts = pre + new_facts + post

    sorts = set(state.sort_for_elt(elt) for elt in elts) - {None}
    assert len(sorts) == 1
    sort = list(sorts)[0]

    i = 0
    renaming = {}
    for elt in elts:
        if state.sort_for_elt(elt) is not None:
            renaming[elt] = '%s%s' % (sort, i)
            i += 1

    rename_state(state, renaming)


def filter_trace(trace: Trace) -> None:
    for state in trace.states:
        filter_negative_facts(state)
        substitute_constants(state)
        filter_total_order_facts('le', state)

def pretty_state(state: State, old_news: Set[str]=set()) -> List[str]:
    lines = []
    lines.append('exists %s.' % (', '.join(sorted(state.universe)),))
    for c in sorted(state.conjuncts):
        if c in old_news or old_news == set():
            lines.append('  ' + c)
        else:
            lines.append('* ' + c)

    return lines

def pretty_trace(trace: Trace) -> str:
    lines = []
    previous: Set[str] = set()
    for i in range(len(trace.states)):
        lines.append('state %s:' % (i,))
        lines.extend(pretty_state(trace.states[i], old_news=previous))
        previous = set(trace.states[i].conjuncts)
        if i < len(trace.actions):
            lines.append('')
            lines.append(trace.actions[i])
            lines.append('')
        i += 1

    return '\n'.join(lines)

def main() -> None:
    # open the log
    # split abstract trace into states
    # filter out negative tuples
    # filter out inequalities
    # substitute constants
    # some kind of smart matching for alpha renaming?

    with open('log.no1a.nodq.2nodes') as f:
        trace = parse_trace(f)



if __name__ == '__main__':
    main()
