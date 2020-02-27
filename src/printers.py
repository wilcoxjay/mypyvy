from collections import defaultdict
from dataclasses import dataclass

import syntax
from syntax import UninterpretedSort, SortDecl, ConstantDecl, RelationDecl, FunctionDecl
import logic
from logic import State

from typing import List, Dict, Optional, Set, Union

def get_sort(name: str) -> SortDecl:
    prog = syntax.the_program
    s = prog.scope.get_sort(name)
    assert s is not None, (name, s)
    return s

def get_constant(name: str) -> ConstantDecl:
    prog = syntax.the_program
    c = prog.scope.get(name)
    assert isinstance(c, ConstantDecl), (name, c)
    return c

def is_relation(name: str) -> bool:
    prog = syntax.the_program
    r = prog.scope.get(name)
    return isinstance(r, RelationDecl)

def get_relation(name: str) -> RelationDecl:
    prog = syntax.the_program
    r = prog.scope.get(name)
    assert isinstance(r, RelationDecl), (name, r)
    return r

def is_function(name: str) -> bool:
    prog = syntax.the_program
    f = prog.scope.get(name)
    return isinstance(f, FunctionDecl)

def get_function(name: str) -> FunctionDecl:
    prog = syntax.the_program
    f = prog.scope.get(name)
    assert isinstance(f, FunctionDecl), (name, f)
    return f

def get_ordinal(state: State, order: RelationDecl, elt: str) -> int:
    graph: Dict[str, Set[str]] = defaultdict(set)
    for tup, b in state.rel_interp[order]:
        if b:
            assert len(tup) == 2
            lo, hi = tup
            graph[hi].add(lo)

    assert elt in graph
    return len(graph[elt]) - 1

def ordered_by_printer(state: State, s: SortDecl, elt: str, args: List[str]) -> str:
    assert len(args) == 1
    order_name = args[0]
    order = get_relation(order_name)
    us = UninterpretedSort(s.name)
    assert order.arity == [us, us] and not order.mutable

    return '%s%s' % (s.name, get_ordinal(state, order, elt))

def set_printer(state: State, s: SortDecl, elt: str, args: List[str]) -> str:
    assert len(args) == 1
    member_name = args[0]
    member = get_relation(member_name)

    assert len(member.arity) == 2 and not member.mutable
    set_sort = UninterpretedSort(s.name)
    assert member.arity[1] == set_sort
    item_sort = member.arity[0]
    item_sort_decl = syntax.get_decl_from_sort(item_sort)

    items: Set[str] = set()
    for tup, b in state.rel_interp[member]:
        assert len(tup) == 2
        item, set_id = tup
        if b and set_id == elt:
            items.add(item)

    return '{%s}' % (','.join(sorted(logic.print_element(state, item_sort_decl, x) for x in items)),)

def const_printer(state: State, s: SortDecl, elt: str, args: List[str]) -> str:
    prog = syntax.the_program
    for c in prog.constants():
        if syntax.get_decl_from_sort(c.sort) == s and state.const_interp[c] == elt:
            return c.name

    return elt

def option_printer(state: State, s: SortDecl, elt: str, args: List[str]) -> str:
    assert len(args) == 2
    is_none_name, value_name = args
    is_none = get_relation(is_none_name)
    value = get_function(value_name)

    option_sort = UninterpretedSort(s.name)

    assert not is_none.mutable and not value.mutable and \
        is_none.arity == [option_sort] and value.arity == [option_sort]

    elt_sort = syntax.get_decl_from_sort(value.sort)

    none: Optional[str] = None
    for tup, b in state.rel_interp[is_none]:
        if b:
            assert none is None and len(tup) == 1
            none = tup[0]

    assert none is not None

    if elt == none:
        return 'None'
    else:
        the_value: Optional[str] = None
        for tup, res in state.func_interp[value]:
            assert len(tup) == 1
            if tup[0] == elt:
                assert the_value is None
                the_value = res
        assert the_value is not None

        return 'Some(%s)' % (logic.print_element(state, elt_sort, the_value))

@dataclass
class LogEntry(object):
    index: str
    # Contents of the different fields of this log entry.
    # Each element of the list is itself a list because
    # it may be based on a relation, and a not well-formed
    # log might have multiple values for a given field.
    values: List[List[str]]

# Generic printer for logs.
# args[0] should give the name of the relation giving a total order over the index sort.
# args[1] should give a relation of type used(s, args[0]) specifying whether an
# index is used for the given log.
# args[i] for i > 1 should give names of either relations of
# type r(args[0], some_sort) or functions of type f(args[0]): some_sort.
# These functions and relations give the elements at each index.
# This printer assumes that there is a function
def log_printer(state: State, s: SortDecl, elt: str, args: List[str]) -> str:
    # args should at least hold an index total order and used relation
    assert len(args) > 1
    n_values = len(args) - 2

    index_le = get_relation(args[0])
    assert len(index_le.arity) == 2
    assert index_le.arity[0] == index_le.arity[1] and not index_le.mutable
    index_sort = syntax.get_decl_from_sort(index_le.arity[0])
    index_used = get_relation(args[1])

    def default_values() -> List[List[str]]:
        return [[] for x in range(n_values)]

    def assert_valid_rel_or_func(rel_or_func: Union[RelationDecl, FunctionDecl]) -> None:
        assert len(rel_or_func.arity) >= 2
        assert isinstance(rel_or_func.arity[0], UninterpretedSort)
        assert isinstance(rel_or_func.arity[1], UninterpretedSort)
        assert rel_or_func.arity[0].decl == s
        assert rel_or_func.arity[1].decl == index_sort

    entries: Dict[str, LogEntry] = {}
    for tup, b in state.rel_interp[index_used]:
        if not b:
            continue

        log, index = tup
        if log == elt and index not in entries:
            entries[index] = LogEntry(index, values=default_values())

    value_sorts: List[SortDecl] = []
    for idx, name in enumerate(args[2:]):
        if is_relation(name):
            val_rel = get_relation(name)
            assert_valid_rel_or_func(val_rel)
            value_sorts.append(syntax.get_decl_from_sort(val_rel.arity[2]))
            for tup, b in state.rel_interp[val_rel]:
                if not b:
                    continue

                log, index, value = tup
                if log == elt:
                    if index not in entries:
                        entries[index] = LogEntry(index, default_values())
                    entries[index].values[idx].append(value)
        else:
            val_func = get_function(name)
            assert_valid_rel_or_func(val_func)
            value_sorts.append(syntax.get_decl_from_sort(val_func.sort))
            for tup, res in state.func_interp[val_func]:
                log, index = tup
                if log == elt:
                    if index not in entries:
                        entries[index] = LogEntry(index, default_values())
                    entries[index].values[idx].append(res)

    # The printed value of an index is consistent with index_le, so the log
    # should be ordered in the same way.
    sorted_entries = sorted(entries.values(),
                            key=lambda e: get_ordinal(state, index_le, e.index))

    # A log is well-formed if it is empty or
    #  all entries have a single element for each value and the set of indexes
    #  has no gaps starting from zero.
    well_formed = ((not sorted_entries) or
                   (all(all(len(x) == 1 for x in e.values) for e in sorted_entries) and
                    get_ordinal(state, index_le, sorted_entries[-1].index) ==
                    len(sorted_entries) - 1))

    def value_to_str(vs: List[str], sort: SortDecl) -> str:
        return '%s |-> %s' % (
            sort.name,
            logic.print_element(state, sort, vs[0]) if len(vs) == 1 else
            '[%s]' % (', '.join(logic.print_element(state, sort, v) for v in vs)))

    def entry_to_str(e: LogEntry, wf: bool) -> str:
        entry_strs = [value_to_str(e.values[idx], sort) for idx, sort in enumerate(value_sorts)]
        if not wf:
            entry_strs.insert(0, 'index |-> %s' % logic.print_element(state, index_sort, e.index))
        return '[%s]' % (', '.join(entry_strs))

    return '<<%s>>' % (', '.join(entry_to_str(entry, well_formed) for entry in sorted_entries))
