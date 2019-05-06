from collections import defaultdict
from dataclasses import dataclass

from syntax import UninterpretedSort, SortDecl, ConstantDecl, RelationDecl, FunctionDecl
from logic import Model

from typing import List, Dict, Optional, Set

def get_sort(m: Model, name: str) -> SortDecl:
    s = m.prog.scope.get_sort(name)
    assert s is not None, (name, s)
    return s

def get_constant(m: Model, name: str) -> ConstantDecl:
    c = m.prog.scope.get(name)
    assert isinstance(c, ConstantDecl), (name, c)
    return c

def get_relation(m: Model, name: str) -> RelationDecl:
    r = m.prog.scope.get(name)
    assert isinstance(r, RelationDecl), (name, r)
    return r

def get_function(m: Model, name: str) -> FunctionDecl:
    f = m.prog.scope.get(name)
    assert isinstance(f, FunctionDecl), (name, f)
    return f

def get_ordinal(m: Model, order: RelationDecl, elt: str) -> int:
    graph: Dict[str, Set[str]] = defaultdict(set)
    for tup, b in m.immut_rel_interps[order]:
        if b:
            assert len(tup) == 2
            lo, hi = tup
            graph[hi].add(lo)

    assert elt in graph
    return len(graph[elt]) - 1

def ordered_by_printer(m: Model, s: SortDecl, elt: str, args: List[str]) -> str:
    assert len(args) == 1
    order_name = args[0]
    order = get_relation(m, order_name)
    us = UninterpretedSort(None, s.name)
    assert order.arity == [us, us] and not order.mutable

    return '%s%s' % (s.name, get_ordinal(m, order, elt))

def set_printer(m: Model, s: SortDecl, elt: str, args: List[str]) -> str:
    assert len(args) == 1
    member_name = args[0]
    member = get_relation(m, member_name)

    assert len(member.arity) == 2 and not member.mutable
    set_sort = UninterpretedSort(None, s.name)
    assert member.arity[1] == set_sort
    item_sort = member.arity[0]
    assert isinstance(item_sort, UninterpretedSort) and item_sort.decl is not None
    item_sort_decl = item_sort.decl

    items: Set[str] = set()
    for tup, b in m.immut_rel_interps[member]:
        assert len(tup) == 2
        item, set_id = tup
        if b and set_id == elt:
            items.add(item)

    return '{%s}' % (','.join(sorted(m.print_element(item_sort_decl, x) for x in items)),)

def option_printer(m: Model, s: SortDecl, elt: str, args: List[str]) -> str:
    assert len(args) == 2
    is_none_name, value_name = args
    is_none = get_relation(m, is_none_name)
    value = get_function(m, value_name)

    option_sort = UninterpretedSort(None, s.name)

    assert not is_none.mutable and not value.mutable and \
        is_none.arity == [option_sort] and value.arity == [option_sort]

    elt_sort_us = value.sort
    assert isinstance(elt_sort_us, UninterpretedSort) and elt_sort_us.decl is not None
    elt_sort = elt_sort_us.decl

    none: Optional[str] = None
    for tup, b in m.immut_rel_interps[is_none]:
        if b:
            assert none is None and len(tup) == 1
            none = tup[0]

    assert none is not None

    if elt == none:
        return 'None'
    else:
        the_value: Optional[str] = None
        for tup, res in m.immut_func_interps[value]:
            assert len(tup) == 1
            if tup[0] == elt:
                assert the_value is None
                the_value = res
        assert the_value is not None

        return 'Some(%s)' % (m.print_element(elt_sort, the_value))

@dataclass
class RaftEntry(object):
    index: str
    terms: List[str]
    value: Optional[str]

def raft_log_printer(m: Model, s: SortDecl, elt: str, args: List[str]) -> str:
    index_sort = get_sort(m, 'index')
    term_sort = get_sort(m, 'term')
    value_sort = get_sort(m, 'value')

    index_used = get_relation(m, 'index_used')
    term_at = get_relation(m, 'term_at')
    value_at = get_function(m, 'value_at')
    index_le = get_relation(m, 'index_le')

    def dedup(l: List[str]) -> List[str]:
        return list(dict.fromkeys(l))

    entries: Dict[str, RaftEntry] = {}
    for tup, b in m.immut_rel_interps[term_at]:
        if not b:
            continue

        log, index, term = tup
        if log == elt:
            if index in entries:
                entries[index].terms.append(term)
            else:
                entries[index] = RaftEntry(index, [term], value=None)

    for tup, b in m.immut_rel_interps[index_used]:
        if not b:
            continue

        log, index = tup
        if log == elt and index not in entries:
            entries[index] = RaftEntry(index, terms=[], value=None)

    for tup, res in m.immut_func_interps[value_at]:
        log, index = tup
        if log == elt and index in entries:
            entries[index].value = res

    # The printed value of an index is consistent with index_le, so the log
    # should be ordered in the same way.
    sorted_entries = sorted(entries.values(),
                            key=lambda e: get_ordinal(m, index_le, e.index))

    # A log is well-formed if it is empty or
    #  all entries have a single term and the set of indexes
    #  has no gaps starting from zero.
    well_formed = ((not sorted_entries) or
                   (all(map(lambda e: len(e.terms) == 1, sorted_entries)) and
                    get_ordinal(m, index_le, sorted_entries[-1].index) ==
                    len(sorted_entries) - 1))

    def entry_to_str(e: RaftEntry, wf: bool) -> str:
        assert e.value is not None

        if wf:
            assert len(e.terms) == 1

            return '[term |-> %s, value |-> %s]' % (
                m.print_element(term_sort, e.terms[0]),
                m.print_element(value_sort, e.value))
        else:
            return '[index |-> %s, term |-> %s, value |-> %s]' % (
                m.print_element(index_sort, e.index),
                '[%s]' % (', '.join(m.print_element(term_sort, t) for t in e.terms)),
                m.print_element(value_sort, e.value))

    return '<<%s>>' % (', '.join(entry_to_str(entry, well_formed) for entry in sorted_entries))
