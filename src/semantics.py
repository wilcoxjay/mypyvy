'''
This module defines class Trace, which gives the semantics to
multi-vocabulary formulas, and a convenience class State.
'''

from __future__ import annotations
from dataclasses import dataclass
from itertools import chain, product, combinations
import re
from typing import List, Optional, Tuple, Union, Dict, cast
from abc import ABC, abstractmethod

import utils
import typechecker
import syntax
from syntax import Expr, ConstantDecl, RelationDecl, FunctionDecl, SortDecl

Element = str
Universe = Dict[SortDecl, Tuple[Element, ...]]  # ODED: I think this should be Sort or str, rather than SortDecl. The universe does not interpret sorts like Int or Bool (I think).
RelationInterp = Dict[Tuple[Element, ...], bool]
FunctionInterp = Dict[Tuple[Element, ...], Element]
RelationInterps = Dict[RelationDecl, RelationInterp]
ConstantInterps = Dict[ConstantDecl, Element]
FunctionInterps = Dict[FunctionDecl, FunctionInterp]


class FirstOrderStructure(ABC):
    '''
    This is an abstract base class for anything that implements a
    first-order structure. The structure is not guaranteed to
    interpret all of the program's vocabulary. For example, some
    subclasses interpret both mutable and immutable symbols, which
    others interpret only the immutable ones. Thus, the vocabulary of
    the structure is implictly given by the keys of the dictionaries.
    '''
    @property
    @abstractmethod
    def univs(self) -> Universe:
        ...

    @property
    @abstractmethod
    def rel_interps(self) -> RelationInterps:
        ...

    @property
    @abstractmethod
    def const_interps(self) -> ConstantInterps:
        ...

    @property
    @abstractmethod
    def func_interps(self) -> FunctionInterps:
        ...

    # TODO: when everything is a function, all three properties above
    # can just be merged into one interp property, or better yet, all
    # four above can just become an overloaded __getitem__ method.


@dataclass
class BareFirstOrderStructure(FirstOrderStructure):
    '''This class represents a bare first-order structure, whose symbols
    need not be related to the program, and whose properties are given
    by simple dictionaries. Example uses include representing the
    model obtained from an SMT solver.

    Note that not all element tuples have to be in the interpretation
    for every relation/function. That is, the structure can be
    partial.

    '''
    _univs: Universe
    _rel_interps: RelationInterps
    _const_interps: ConstantInterps
    _func_interps: FunctionInterps

    @property
    def univs(self) -> Universe:
        return self._univs

    @property
    def rel_interps(self) -> RelationInterps:
        return self._rel_interps

    @property
    def const_interps(self) -> ConstantInterps:
        return self._const_interps

    @property
    def func_interps(self) -> FunctionInterps:
        return self._func_interps


class Trace:
    def __init__(
            self,
            num_states: int,
    ) -> None:
        assert num_states >= 0
        self.num_states = num_states

        self.univs: Universe = {}

        self.immut_rel_interps: RelationInterps = {}
        self.immut_const_interps: ConstantInterps = {}
        self.immut_func_interps: FunctionInterps = {}

        self.rel_interps: List[RelationInterps] = [{} for i in range(self.num_states)]
        self.const_interps: List[ConstantInterps] = [{} for i in range(self.num_states)]
        self.func_interps: List[FunctionInterps] = [{} for i in range(self.num_states)]

        self.transitions: List[str] = ['' for i in range(self.num_states - 1)]
        self.onestate_formula_cache: Dict[int, Expr] = {}

    def _as_trace(self, indices: Tuple[int, ...]) -> Trace:
        assert all(0 <= i < self.num_states for i in indices)
        assert indices in [(1, 0), (1,), tuple(reversed(range(len(indices))))], 'should only be used in legacy pd.py code'
        t = Trace(len(indices))
        t.univs = self.univs.copy()
        t.immut_rel_interps = self.immut_rel_interps.copy()
        t.immut_const_interps = self.immut_const_interps.copy()
        t.immut_func_interps = self.immut_func_interps.copy()
        t.rel_interps = [self.rel_interps[i].copy() for i in indices]
        t.const_interps = [self.const_interps[i].copy() for i in indices]
        t.func_interps = [self.func_interps[i] for i in indices]
        # no transition labels in permuted trace
        return t

    def __str__(self) -> str:
        l = []
        dummy_state = State(self, None)
        l.extend(_univ_str(dummy_state))
        l.append(_struct_str(dummy_state))
        for i in range(self.num_states):
            if i > 0 and self.transitions[i - 1] != '':
                l.append('\ntransition %s' % (self.transitions[i - 1],))
            l.append('\nstate %s:' % (i,))
            l.append(_struct_str(State(self, i), print_immutable=False))

        return '\n'.join(l)

    def as_onestate_formula(self, index: Optional[int] = None) -> Expr:
        # TODO: move to class State, this shouldn't be here
        assert self.num_states == 1 or index is not None, \
            'to generate a onestate formula from a multi-state model, ' + \
            'you must specify which state you want'
        assert index is None or (0 <= index and index < self.num_states)

        if index is None:
            index = 0

        if index not in self.onestate_formula_cache:
            prog = syntax.the_program

            mut_rel_interps = self.rel_interps[index]
            mut_const_interps = self.const_interps[index]
            mut_func_interps = self.func_interps[index]

            vs: List[syntax.SortedVar] = []
            ineqs: Dict[SortDecl, List[Expr]] = {}
            rels: Dict[RelationDecl, List[Expr]] = {}
            consts: Dict[ConstantDecl, Expr] = {}
            funcs: Dict[FunctionDecl, List[Expr]] = {}
            for sort in self.univs:
                vs.extend(syntax.SortedVar(v, syntax.UninterpretedSort(sort.name))
                          for v in self.univs[sort])
                u = [syntax.Id(v) for v in self.univs[sort]]
                ineqs[sort] = [syntax.Neq(a, b) for a, b in combinations(u, 2)]
            for R, l in chain(mut_rel_interps.items(), self.immut_rel_interps.items()):
                rels[R] = []
                for tup, ans in l.items():
                    e: Expr = (
                        syntax.AppExpr(R.name, tuple(syntax.Id(col) for col in tup))
                        if tup else syntax.Id(R.name)
                    )
                    rels[R].append(e if ans else syntax.Not(e))
            for C, c in chain(mut_const_interps.items(), self.immut_const_interps.items()):
                consts[C] = syntax.Eq(syntax.Id(C.name), syntax.Id(c))
            for F, fl in chain(mut_func_interps.items(), self.immut_func_interps.items()):
                funcs[F] = [
                    syntax.Eq(syntax.AppExpr(F.name, tuple(syntax.Id(col) for col in tup)),
                              syntax.Id(res))
                    for tup, res in fl.items()
                ]

            # get a fresh variable, avoiding names of universe elements in vs
            fresh = prog.scope.fresh('x', [v.name for v in vs])

            e = syntax.Exists(tuple(vs), syntax.And(
                *chain(*ineqs.values(), *rels.values(), consts.values(), *funcs.values(), (
                    syntax.Forall((syntax.SortedVar(fresh,
                                                    syntax.UninterpretedSort(sort.name)),),
                                  syntax.Or(*(syntax.Eq(syntax.Id(fresh), syntax.Id(v))
                                              for v in self.univs[sort])))
                    for sort in self.univs
                ))))
            assert prog.scope is not None
            with prog.scope.n_states(1):
                typechecker.typecheck_expr(prog.scope, e, None)
            self.onestate_formula_cache[index] = e
        return self.onestate_formula_cache[index]

    def as_state(self, i: int) -> State:
        assert 0 <= i < self.num_states
        return State(self, i)

    def eval(self, full_expr: Expr, starting_index: Optional[int]) -> Union[Element, bool]:
        # this function assumes expr does not contain macros (i.e., macros have been expanded)
        def go(expr: Expr, index: Optional[int]) -> Union[Element, bool]:
            assert index is None or 0 <= index < self.num_states

            def get_rel(d: RelationDecl) -> RelationInterp:
                if d.mutable:
                    assert index is not None
                    return self.rel_interps[index][d]
                else:
                    return self.immut_rel_interps[d]

            def get_const(d: ConstantDecl) -> Element:
                if d.mutable:
                    assert index is not None
                    return self.const_interps[index][d]
                else:
                    return self.immut_const_interps[d]

            def get_func(d: FunctionDecl) -> FunctionInterp:
                if d.mutable:
                    assert index is not None
                    return self.func_interps[index][d]
                else:
                    return self.immut_func_interps[d]
            # TODO: rewrite to use the new resolved expr without traversing with scope
            scope: syntax.Scope[Union[Element, bool]] = cast(
                syntax.Scope[Union[Element, bool]],
                syntax.the_program.scope
            )
            if isinstance(expr, syntax.Bool):
                return expr.val
            elif isinstance(expr, syntax.UnaryExpr):
                if expr.op == 'NEW':
                    assert index is not None
                    with scope.next_state_index():
                        return go(expr.arg, index=index + 1)
                elif expr.op == 'NOT':
                    return not go(expr.arg, index)
                else:
                    assert False, f'eval unknown operation {expr.op}'
            elif isinstance(expr, syntax.BinaryExpr):
                if expr.op == 'IMPLIES':
                    return not go(expr.arg1, index) or go(expr.arg2, index)
                elif expr.op in ['IFF', 'EQUAL']:
                    return go(expr.arg1, index) == go(expr.arg2, index)
                elif expr.op == 'NOTEQ':
                    return go(expr.arg1, index) != go(expr.arg2, index)
                else:
                    assert False, expr
            elif isinstance(expr, syntax.NaryExpr):
                assert expr.op in ['AND', 'OR', 'DISTINCT']
                if expr.op in ['AND', 'OR']:
                    p = all if expr.op == 'AND' else any
                    return p(go(arg, index) for arg in expr.args)
                else:
                    assert expr.op == 'DISTINCT'
                    return len(set(go(arg, index) for arg in expr.args)) == len(expr.args)
            elif isinstance(expr, syntax.AppExpr):
                args = tuple(cast(Element, go(arg, index)) for arg in expr.args)
                assert all(isinstance(a, Element) for a in args)
                d = scope.get(expr.callee)
                if isinstance(d, RelationDecl):
                    return get_rel(d)[args]
                elif isinstance(d, FunctionDecl):
                    return get_func(d)[args]
                else:
                    assert False, f'{d}\n{expr}'
            elif isinstance(expr, syntax.QuantifierExpr):
                assert expr.quant in ['FORALL', 'EXISTS']
                p = all if expr.quant == 'FORALL' else any
                doms = [self.univs[syntax.get_decl_from_sort(sv.sort)] for sv in expr.binder.vs]

                def one(q: syntax.QuantifierExpr, tup: Tuple[str, ...]) -> bool:
                    with scope.in_scope(q.binder, list(tup)):
                        ans = go(q.body, index)
                        assert isinstance(ans, bool)
                        return ans
                return p(one(expr, t) for t in product(*doms))
            elif isinstance(expr, syntax.Id):
                a = scope.get(expr.name)
                # definitions are not supported
                assert (not isinstance(a, syntax.DefinitionDecl) and
                        not isinstance(a, syntax.FunctionDecl) and a is not None)
                if isinstance(a, syntax.RelationDecl):
                    return get_rel(a)[()]
                elif isinstance(a, syntax.ConstantDecl):
                    return get_const(a)
                elif isinstance(a, tuple):
                    # bound variable introduced to scope
                    (bound_elem,) = a
                    return bound_elem
                else:
                    assert isinstance(a, str) or isinstance(a, bool)
                    return a
            elif isinstance(expr, syntax.IfThenElse):
                branch = go(expr.branch, index)
                assert isinstance(branch, bool)
                return go(expr.then, index) if branch else go(expr.els, index)
            elif isinstance(expr, syntax.Let):
                val = go(expr.val, index)
                with scope.in_scope(expr.binder, [val]):
                    return go(expr.body, index)
            else:
                assert False, expr

        return go(full_expr, index=starting_index)


@dataclass
class State(FirstOrderStructure):
    trace: Trace
    index: Optional[int]  # TODO: make it non-optional. it's only used in the printer

    @property
    def univs(self) -> Universe:
        return self.trace.univs

    @property
    def immut_rel_interps(self) -> RelationInterps:
        return self.trace.immut_rel_interps

    @property
    def immut_const_interps(self) -> ConstantInterps:
        return self.trace.immut_const_interps

    @property
    def immut_func_interps(self) -> FunctionInterps:
        return self.trace.immut_func_interps

    @property
    def mut_rel_interps(self) -> RelationInterps:
        return self.trace.rel_interps[self.index] if self.index is not None else {}

    @property
    def mut_const_interps(self) -> ConstantInterps:
        return self.trace.const_interps[self.index] if self.index is not None else {}

    @property
    def mut_func_interps(self) -> FunctionInterps:
        return self.trace.func_interps[self.index] if self.index is not None else {}

    # TODO: the following involve redundent copying. we can revisit if
    # they hinder performance (e.g., make them a function getting the
    # rel/const/func instead of returning a dict)
    @property
    def rel_interps(self) -> RelationInterps:
        return {**self.immut_rel_interps, **self.mut_rel_interps}

    @property
    def const_interps(self) -> ConstantInterps:
        return {**self.immut_const_interps, **self.mut_const_interps}

    @property
    def func_interps(self) -> FunctionInterps:
        return {**self.immut_func_interps, **self.mut_func_interps}

    def __repr__(self) -> str:
        return '\n'.join(_univ_str(self) + [_struct_str(self, print_negative_tuples=True, print_immutable=True)])

    def __str__(self) -> str:
        return '\n'.join(_univ_str(self) + [_struct_str(self, print_immutable=True)])

    def eval(self, e: Expr) -> Union[str, bool]:
        # TODO: assert that e is a single vocabulary formula
        return self.trace.eval(e, starting_index=self.index)

    def as_onestate_formula(self) -> Expr:
        return self.trace.as_onestate_formula(index=self.index)

    def element_sort(self, element_name: str) -> SortDecl:
        # TODO: eliminate this function
        matching_sorts = [s for s, u in self.univs.items() if element_name in u]
        assert matching_sorts, f'unknown element name: {element_name}'
        assert len(matching_sorts) == 1, f'ambiguous element name: {element_name}'
        return matching_sorts[0]


def try_printed_by(struct: FirstOrderStructure, s: SortDecl, elt: str) -> Optional[str]:
    custom_printer_annotation = syntax.get_annotation(s, 'printed_by')

    if custom_printer_annotation is not None:
        assert len(custom_printer_annotation.args) >= 1
        import importlib
        printers = importlib.import_module('printers')
        printer_name = custom_printer_annotation.args[0]
        custom_printer = printers.__dict__.get(printer_name)
        custom_printer_args = custom_printer_annotation.args[1:] \
            if custom_printer is not None else []
        if custom_printer is not None:
            return custom_printer(struct, s, elt, custom_printer_args)
        else:
            utils.print_warning(custom_printer_annotation.span,
                                'could not find printer named %s' % (printer_name,))
    return None


def print_element(struct: FirstOrderStructure, s: Union[SortDecl, syntax.Sort], elt: Element) -> str:
    if not isinstance(s, SortDecl):
        if isinstance(s, (syntax._BoolSort, syntax._IntSort)):
            return elt
        s = syntax.get_decl_from_sort(s)

    return try_printed_by(struct, s, elt) or elt


def print_tuple(struct: FirstOrderStructure, arity: Tuple[syntax.Sort, ...], tup: Tuple[Element, ...]) -> str:
    l = []
    assert len(arity) == len(tup)
    for s, x in zip(arity, tup):
        l.append(print_element(struct, s, x))
    return ','.join(l)


_digits_re = re.compile(r'(?P<prefix>.*?)(?P<suffix>[0-9]+)$')
def _univ_str(struct: FirstOrderStructure) -> List[str]:
    l = []
    for s in sorted(struct.univs.keys(), key=str):
        if syntax.has_annotation(s, 'no_print'):
            continue

        l.append(str(s))

        def key(x: str) -> Tuple[str, int]:
            ans = print_element(struct, s, x)
            if (m := _digits_re.match(ans)) is not None:
                return (m['prefix'], int(m['suffix']))
            else:
                return (ans, 0)
        for x in sorted(struct.univs[s], key=key):
            l.append('  %s' % print_element(struct, s, x))
    return l


def _struct_str(
        struct: FirstOrderStructure,
        print_immutable: bool = True,
        print_negative_tuples: Optional[bool] = None,
) -> str:
    if print_negative_tuples is None:
        print_negative_tuples = utils.args.print_negative_tuples

    l = []

    Cs = struct.const_interps
    for C in Cs:
        if syntax.has_annotation(C, 'no_print') or (not C.mutable and not print_immutable):
            continue
        l.append('%s = %s' % (C.name, print_element(struct, C.sort, Cs[C])))

    Rs = struct.rel_interps
    for R in Rs:
        if syntax.has_annotation(R, 'no_print') or (not R.mutable and not print_immutable):
            continue
        for tup, b in sorted(Rs[R].items(), key=lambda x: print_tuple(struct, R.arity, x[0])):
            if b or print_negative_tuples:
                l.append('%s%s(%s)' % ('' if b else '!', R.name,
                                       print_tuple(struct, R.arity, tup)))

    Fs = struct.func_interps
    for F in Fs:
        if syntax.has_annotation(F, 'no_print') or (not F.mutable and not print_immutable):
            continue
        for tup, res in sorted(Fs[F].items(), key=lambda x: print_tuple(struct, F.arity, x[0])):
            l.append('%s(%s) = %s' % (F.name, print_tuple(struct, F.arity, tup),
                                      print_element(struct, F.sort, res)))

    return '\n'.join(l)
