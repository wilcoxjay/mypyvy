from __future__ import annotations

import z3_utils

from contextlib import contextmanager
from copy import copy
from dataclasses import dataclass
import functools
import itertools
import ply.lex
from typing import List, Union, Tuple, Optional, Dict, Iterator, \
    Callable, Any, Set, TypeVar, Generic, Iterable, Mapping, Sequence, cast
from typing_extensions import Protocol
import utils
import z3
from networkx import DiGraph  # type: ignore

Token = ply.lex.LexToken
Span = Tuple[Token, Token]

B = TypeVar('B')

class Denotable(object):
    def __init__(self) -> None:
        self._hash: Optional[int] = None

    def _denote(self) -> Tuple:
        raise Exception('Unexpected denotable object %s does not implement _denote method' % repr(self))

    def __getstate__(self) -> Any:
        return dict(
            self.__dict__,
            _hash=None,
        )

    def __hash__(self) -> int:
        if self._hash is None:
            self._hash = hash((type(self), self._denote()))
        return self._hash

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Denotable):
            return False

        return (type(self) is type(other) and
                self._denote() == other._denote())


class Sort(Denotable):
    def __init__(self) -> None:
        super().__init__()

    def __repr__(self) -> str:
        raise Exception('Unexpected sort %s does not implement __repr__ method' % type(self))

    def __str__(self) -> str:
        raise Exception('Unexpected sort %s does not implement __str__ method' % repr(self))

    def resolve(self, scope: Scope[B]) -> None:
        raise Exception('Unexpected sort %s does not implement resolve method' % repr(self))

    def to_z3(self) -> z3.SortRef:
        raise Exception('Unexpected sort %s does not implement to_z3 method' % repr(self))

    def __ne__(self, other: object) -> bool:
        return not (self == other)


class HasSortField(Protocol):
    sort: InferenceSort

class SortInferencePlaceholder(object):
    def __init__(self, d: Optional[HasSortField]=None) -> None:
        self.backpatches: List[HasSortField] = []
        self.sort: Optional[Sort] = None
        self.parent: Optional[SortInferencePlaceholder] = None

        if d is not None:
            self.add(d)

    def add(self, d: HasSortField) -> None:
        self.backpatches.append(d)

    def root(self) -> SortInferencePlaceholder:
        if self.parent is not None:
            return self.parent.root()
        else:
            return self

    def solve(self, sort: Sort) -> None:
        assert self.parent is None
        assert self.sort is None

        self.sort = sort

        for d in self.backpatches:
            d.sort = sort

    def merge(self, other: SortInferencePlaceholder) -> None:
        assert self.parent is None
        assert other.parent is None
        assert self.sort is None
        assert other.sort is None
        if self == other:
            return

        other.parent = self
        self.backpatches.extend(other.backpatches)

InferenceSort = Union[Sort, SortInferencePlaceholder, None]


PREC_BOT = 0
PREC_NOT = 1
PREC_EQ = 2
PREC_AND = 3
PREC_OR = 4
PREC_IMPLIES = 5
PREC_IFF = 6
PREC_QUANT = 7
PREC_TOP = 8

PREC_ASSOC = {
    PREC_BOT: 'NONE',
    PREC_NOT: 'NONE',
    PREC_EQ: 'NONE',
    PREC_AND: 'LEFT',
    PREC_OR: 'LEFT',
    PREC_IMPLIES: 'RIGHT',
    PREC_IFF: 'NONE',
    PREC_QUANT: 'NONE',
    PREC_TOP: 'NONE'
}

def no_parens(ip: int, op: int, side: str) -> bool:
    return ip < op or (ip == op and side == PREC_ASSOC[ip])

class Z3Translator(object):
    def __init__(self, scope: Scope[z3.ExprRef], keys: Tuple[str, ...] = ()) -> None:
        self.scope = scope
        self.keys = keys
        self.counter = 0

    def bind(self, binder: Binder) -> List[z3.ExprRef]:
        bs = []
        for sv in binder.vs:
            n = sv.name + '_%s' % (self.counter,)  # in the presence of shadowing, we need to make sure every call to z3.Const is for a unique name
            self.counter += 1
            assert sv.sort is not None and not isinstance(sv.sort, SortInferencePlaceholder)
            bs.append(z3.Const(n, sv.sort.to_z3()))
        return bs

    def get_key_opt(self, index: int) -> Optional[str]:
        if index < len(self.keys):
            return self.keys[index]
        else:
            return None

    def translate_expr(self, expr: Expr, index: int=0) -> z3.ExprRef:
        if isinstance(expr, Bool):
            return z3.BoolVal(expr.val)
        elif isinstance(expr, UnaryExpr):
            if expr.op == 'NEW':
                assert index + 1 < len(self.keys)
                return self.translate_expr(expr.arg, index=index + 1)
            else:
                unop = z3_UNOPS[expr.op]
                assert unop is not None
                return unop(self.translate_expr(expr.arg, index))
        elif isinstance(expr, BinaryExpr):
            binop = z3_BINOPS[expr.op]
            return binop(self.translate_expr(expr.arg1, index), self.translate_expr(expr.arg2, index))
        elif isinstance(expr, NaryExpr):
            nop = z3_NOPS[expr.op]
            return nop([self.translate_expr(arg, index) for arg in expr.args])
        elif isinstance(expr, AppExpr):
            d = self.scope.get(expr.callee)
            assert d is not None
            if isinstance(d, DefinitionDecl):
                assert index + d.num_states <= len(self.keys)  # checked by resolver; see NOTE(calling-stateful-definitions)
                translated_args = [self.translate_expr(arg, index) for arg in expr.args]  # translate args in the scope of caller
                with self.scope.fresh_stack():
                    with self.scope.in_scope(d.binder, translated_args):
                        return self.translate_expr(d.expr, index)  # translate body of def in fresh scope
            else:
                assert isinstance(d, RelationDecl) or isinstance(d, FunctionDecl)
                k = self.get_key_opt(index)
                assert not d.mutable or k is not None
                R = d.to_z3(k)
                assert isinstance(R, z3.FuncDeclRef)
                app_translated_args = [self.translate_expr(arg, index) for arg in expr.args]
                translated_app = R(*app_translated_args)
                return translated_app
        elif isinstance(expr, QuantifierExpr):
            bs = self.bind(expr.binder)
            with self.scope.in_scope(expr.binder, bs):
                e = self.translate_expr(expr.body, index)
            q = z3.ForAll if expr.quant == 'FORALL' else z3.Exists
            return q(bs, e)
        elif isinstance(expr, Id):
            d = self.scope.get(expr.name)
            assert d is not None
            if isinstance(d, RelationDecl) or \
               isinstance(d, ConstantDecl) or \
               isinstance(d, FunctionDecl):
                k = self.get_key_opt(index)
                assert not d.mutable or k is not None
                x = d.to_z3(k)
                assert isinstance(x, z3.ExprRef)
                return x
            elif isinstance(d, DefinitionDecl):
                assert index + d.num_states <= len(self.keys)  # checked in resolver; see NOTE(calling-stateful-definitions)
                with self.scope.fresh_stack():
                    return self.translate_expr(d.expr, index)
            else:
                e, = d
                return e
        elif isinstance(expr, IfThenElse):
            return z3.If(self.translate_expr(expr.branch, index),
                         self.translate_expr(expr.then, index),
                         self.translate_expr(expr.els, index))
        elif isinstance(expr, Let):
            val = self.translate_expr(expr.val, index)
            with self.scope.in_scope(expr.binder, [val]):
                return self.translate_expr(expr.body, index)
        else:
            assert False, expr


    def frame(self, mods: Iterable[ModifiesClause], index: int = 0) -> List[z3.ExprRef]:
        frame = []
        R: Iterator[StateDecl] = iter(self.scope.relations.values())
        C: Iterator[StateDecl] = iter(self.scope.constants.values())
        F: Iterator[StateDecl] = iter(self.scope.functions.values())
        for d in itertools.chain(R, C, F):
            if not d.mutable or (isinstance(d, RelationDecl) and d.is_derived()) or any(mc.name == d.name for mc in mods):
                continue

            k_new = self.get_key_opt(index + 1)
            k_old = self.get_key_opt(index)
            assert k_new is not None
            assert k_old is not None


            if isinstance(d, ConstantDecl) or len(d.arity) == 0:
                lhs = d.to_z3(k_new)
                rhs = d.to_z3(k_old)
                assert isinstance(lhs, z3.ExprRef) and isinstance(rhs, z3.ExprRef)
                e = lhs == rhs
            else:
                cs: List[z3.ExprRef] = []
                i = 0
                for s in d.arity:
                    cs.append(z3.Const('x' + str(i), s.to_z3()))
                    i += 1

                lhs = d.to_z3(k_new)
                rhs = d.to_z3(k_old)
                assert isinstance(lhs, z3.FuncDeclRef) and isinstance(rhs, z3.FuncDeclRef)

                e = z3.Forall(cs, lhs(*cs) == rhs(*cs))

            frame.append(e)

        return frame

    def translate_transition_body(self, t: DefinitionDecl, precond: Optional[Expr]=None, index: int = 0) -> z3.ExprRef:
        return z3.And(self.translate_expr(t.expr, index=index),
                      *self.frame(t.mods, index=index),
                      self.translate_expr(precond, index=index) if (precond is not None) else z3.BoolVal(True))

    def translate_transition(self, t: DefinitionDecl, precond: Optional[Expr]=None, index: int = 0) -> z3.ExprRef:
        bs = self.bind(t.binder)
        with self.scope.in_scope(t.binder, bs):
            body = self.translate_transition_body(t, precond, index=index)
            if len(bs) > 0:
                return z3.Exists(bs, body)
            else:
                return body

    def translate_precond_of_transition(self, precond: Optional[Expr], t: DefinitionDecl, index: int = 0) -> z3.ExprRef:
        bs = self.bind(t.binder)
        with self.scope.in_scope(t.binder, bs):
            body = self.translate_expr(precond, index=index) if (precond is not None) else z3.BoolVal(True)

            if len(bs) > 0:
                return z3.Exists(bs, body)
            else:
                return body


# Returns a set describing the *mutable* symbols used by an expression.
# Immutable symbols and bound variables are *not* included.
# In the returned set, each element is a tuple (i, ts, s), where
#     - s is the name of the symbol used
#     - ts is a non-empty tuple of tokens describing the sequence of definitions by which
#       expr refers to the symbol s (useful for locating error messages). the tuple is ordered
#       from expr to the direct reference to s. if expr directly refers to s, then the tuple
#       has length one.
#     - i is the "state index" of the usage. in a single-vocabulary formula, this will
#       always be 0, but in a multi-vocabulary formula, it indicates how many new() operators
#       the usage is under.
def symbols_used(scope: Scope, expr: Expr, state_index: int=0) -> Set[Tuple[int, Tuple[Optional[Span], ...], str]]:
    def add_caller_span(s: Set[Tuple[int, Tuple[Optional[Span], ...], str]]) -> Set[Tuple[int, Tuple[Optional[Span], ...], str]]:
        return set((i, (expr.span,) + l, sym) for (i, l, sym) in s)

    if isinstance(expr, Bool):
        return set()
    elif isinstance(expr, UnaryExpr):
        if expr.op == 'NEW':
            return symbols_used(scope, expr.arg, state_index=state_index + 1)
        else:
            return symbols_used(scope, expr.arg, state_index)
    elif isinstance(expr, BinaryExpr):
        return symbols_used(scope, expr.arg1, state_index) | symbols_used(scope, expr.arg2, state_index)
    elif isinstance(expr, NaryExpr):
        ans: Set[Tuple[int, Tuple[Optional[Span], ...], str]] = set()
        for arg in expr.args:
            ans |= symbols_used(scope, arg, state_index)
        return ans
    elif isinstance(expr, AppExpr):
        args: Set[Tuple[int, Tuple[Optional[Span], ...], str]] = set()
        for arg in expr.args:
            args |= symbols_used(scope, arg, state_index)

        d = scope.get(expr.callee)
        assert d is not None and not isinstance(d, tuple)
        if isinstance(d, DefinitionDecl):
            with scope.fresh_stack():
                with scope.in_scope(d.binder, [None for i in range(len(d.binder.vs))]):
                    callee_symbols = symbols_used(scope, d.expr, state_index)
            return args | add_caller_span(callee_symbols)
        elif d.mutable:
            return args | {(state_index, (expr.span,), expr.callee)}
        else:
            return args
    elif isinstance(expr, QuantifierExpr):
        with scope.in_scope(expr.binder, [None for i in range(len(expr.binder.vs))]):
            return symbols_used(scope, expr.body, state_index)
    elif isinstance(expr, Id):
        d = scope.get(expr.name)
        assert d is not None, expr.name
        if isinstance(d, RelationDecl) or \
           isinstance(d, ConstantDecl) or \
           isinstance(d, FunctionDecl):
            return {(state_index, (expr.span,), expr.name)} if d.mutable else set()
        elif isinstance(d, DefinitionDecl):
            with scope.fresh_stack():
                return add_caller_span(symbols_used(scope, d.expr, state_index))
        else:
            return set()
    elif isinstance(expr, IfThenElse):
        return symbols_used(scope, expr.branch, state_index) | \
            symbols_used(scope, expr.then, state_index) | \
            symbols_used(scope, expr.els, state_index)
    elif isinstance(expr, Let):
        s1 = symbols_used(scope, expr.val, state_index)
        with scope.in_scope(expr.binder, [None for i in range(len(expr.binder.vs))]):
            return s1 | symbols_used(scope, expr.body, state_index)
    else:
        assert False


def subst_vars_simple(expr: Expr, subst: Mapping[Id, Expr]) -> Expr:
    if isinstance(expr, Bool):
        return expr
    elif isinstance(expr, UnaryExpr):
        return UnaryExpr(op=expr.op, arg=subst_vars_simple(expr.arg, subst))
    elif isinstance(expr, BinaryExpr):
        return BinaryExpr(op=expr.op, arg1=subst_vars_simple(expr.arg1, subst),
                                                arg2=subst_vars_simple(expr.arg2, subst))
    elif isinstance(expr, AppExpr):
        return AppExpr(callee=expr.callee, args=[subst_vars_simple(a, subst) for a in expr.args])
    elif isinstance(expr, Id):
        return subst.get(expr, expr)
    else:
        print(expr)
        assert False


def xor(b1: bool, b2: bool) -> bool:
    return b1 != b2

def as_clause_body(expr: Expr, negated: bool=False) -> List[List[Expr]]:
    if isinstance(expr, Bool):
        return [[Bool(xor(expr.val, negated))]]
    elif isinstance(expr, UnaryExpr):
        assert expr.op == 'NOT'
        return as_clause_body(expr.arg, not negated)
    elif isinstance(expr, BinaryExpr):
        if expr.op in ['EQUAL', 'NOTEQ']:
            op = 'NOTEQ' if xor(expr.op == 'NOTEQ', negated) else 'EQUAL'
            return [[BinaryExpr(op, expr.arg1, expr.arg2)]]
        else:
            assert expr.op == 'IMPLIES'
            return as_clause_body(Or(Not(expr.arg1), expr.arg2), negated=negated)
    elif isinstance(expr, NaryExpr):
        assert expr.op != 'DISTINCT', 'CNF normalization does not support "distinct" expressions'

        if negated:
            other_op = 'AND' if expr.op == 'OR' else 'OR'
            return as_clause_body(NaryExpr(other_op, [Not(arg) for arg in expr.args]), negated=False)
        elif expr.op == 'AND':
            return list(itertools.chain(*(as_clause_body(arg, negated=False) for arg in expr.args)))
        else:
            assert expr.op == 'OR'
            return [list(itertools.chain(*tup)) for tup in itertools.product(*(as_clause_body(arg, negated=False) for arg in expr.args))]
    elif isinstance(expr, AppExpr) or isinstance(expr, Id):
        if negated:
            return [[Not(expr)]]
        else:
            return [[expr]]
    else:
        assert False, "unsupported expressions %s in as_clause_body" % expr

def as_quant_clauses(expr: Expr, negated: bool=False) -> Tuple[List[SortedVar], List[List[Expr]]]:
    if isinstance(expr, QuantifierExpr):
        if negated:
            other_quant = 'EXISTS' if expr.quant == 'FORALL' else 'FORALL'
            return as_quant_clauses(QuantifierExpr(other_quant, expr.binder.vs, Not(expr.body)), negated=False)
        else:
            assert expr.quant == 'FORALL'
            new_vs, new_body = as_quant_clauses(expr.body, negated=False)
            return expr.binder.vs + new_vs, new_body
    elif isinstance(expr, UnaryExpr) and expr.op == 'NOT':
        return as_quant_clauses(expr.arg, not negated)
    else:
        return [], as_clause_body(expr, negated)

def as_clauses(expr: Expr) -> List[Expr]:
    vs, clauses = as_quant_clauses(expr)
    ans = []
    for clause in clauses:
        if len(clause) == 1:
            clause += [Bool(False)]
        e = Forall(vs, Or(*clause))
        # TODO: should we resolve here? Also, can we not add false?
        # e.resolve(the_program.scope, None)
        ans.append(e)
    return ans

# Produce an expression that guards all the variables in the given binder to be in the
# relation corresponding to their sort. See relativize_quantifiers.
def relativization_guard_for_binder(guards: Mapping[SortDecl, RelationDecl], b: Binder) -> Expr:
    conjs = []
    for v in b.vs:
        guard = Apply(guards[get_decl_from_sort(v.sort)].name, [Id(v.name)])
        conjs.append(guard)
    return And(*conjs)


# 'relativize' an expression by guarding quantifiers by the given relations, which should be
# unary relations of the given sort. The guard relations can be mutable or immutable, but
# note that if they are mutable, then they are always referred to in the "current" state.
#
# For example, if sort node is to be guarded by a relation A, then this would transform the
# expression
#     forall x:node. !(R(x) & S(x))
# into the relativized expression
#     forall x:node. A(x) -> !(R(x) & S(x))
# Universal quantifiers are guarded by implications, while existentials are guarded by
# conjunctions.
def relativize_quantifiers(guards: Mapping[SortDecl, RelationDecl], e: Expr) -> Expr:
    QUANT_GUARD_OP: Dict[str, Callable[[Expr, Expr], Expr]] = {
        'FORALL': Implies,
        'EXISTS': And,
    }

    # TODO: consider supporting a visitor pattern
    def go(e: Expr) -> Expr:
        if isinstance(e, Bool):
            return e
        elif isinstance(e, UnaryExpr):
            return UnaryExpr(e.op, go(e.arg))
        elif isinstance(e, BinaryExpr):
            return BinaryExpr(e.op, go(e.arg1), go(e.arg2))
        elif isinstance(e, NaryExpr):
            return NaryExpr(e.op, [go(arg) for arg in e.args])
        elif isinstance(e, AppExpr):
            return AppExpr(e.callee, [go(arg) for arg in e.args])
        elif isinstance(e, QuantifierExpr):
            guard = relativization_guard_for_binder(guards, e.binder)
            return QuantifierExpr(e.quant, e.binder.vs,
                                  QUANT_GUARD_OP[e.quant](guard, go(e.body)))
        elif isinstance(e, Id):
            return e
        elif isinstance(e, IfThenElse):
            return IfThenElse(go(e.branch), go(e.then), go(e.els))
        elif isinstance(e, Let):
            return Let(e.binder.vs[0], go(e.val), go(e.body))
        else:
            assert False

    return go(e)

# checks if e is a universal formula with one quantifier out front (or is quantifier free)
# i.e. returns false if additional universal quantifiers are buried in the body
def is_universal(e: Expr) -> bool:
    if isinstance(e, QuantifierExpr):
        return e.quant == 'FORALL' and is_quantifier_free(e.body)
    else:
        return is_quantifier_free(e)

def is_quantifier_free(e: Expr) -> bool:
    if isinstance(e, Bool):
        return True
    elif isinstance(e, UnaryExpr):
        return is_quantifier_free(e.arg)
    elif isinstance(e, BinaryExpr):
        return is_quantifier_free(e.arg1) and is_quantifier_free(e.arg2)
    elif isinstance(e, NaryExpr):
        return all(is_quantifier_free(arg) for arg in e.args)
    elif isinstance(e, AppExpr):
        return all(is_quantifier_free(arg) for arg in e.args)
    elif isinstance(e, QuantifierExpr):
        return False
    elif isinstance(e, Id):
        return True
    elif isinstance(e, IfThenElse):
        return (is_quantifier_free(e.branch) and
                is_quantifier_free(e.then) and
                is_quantifier_free(e.els))
    elif isinstance(e, Let):
        return is_quantifier_free(e.val) and is_quantifier_free(e.body)
    else:
        assert False

class HasSpan(Protocol):
    span: Optional[Span]

def span_endlexpos(x: Union[Span, HasSpan]) -> Optional[int]:
    if not isinstance(x, tuple):
        s = x.span
    else:
        s = x

    if s is None:
        return None

    return s[1].lexpos + len(s[1].value)

class FaithfulPrinter(object):
    def __init__(self, prog: Program, ignore_old: bool = False) -> None:
        self.prog = prog
        self.ignore_old = ignore_old
        self.pos = 0
        self.buf: List[str] = []

    def skip_to(self, new_pos: Optional[int]) -> None:
        if new_pos is not None:
            self.pos = new_pos

    def skip_to_start(self, x: HasSpan) -> None:
        assert x.span is not None
        self.skip_to(x.span[0].lexpos)

    def skip_to_end(self, x: HasSpan) -> None:
        self.skip_to(span_endlexpos(x))

    def move_to(self, new_pos: Optional[int]) -> None:
        assert self.prog.input is not None
        if new_pos is None:
            return
        assert self.pos <= new_pos
        if self.pos < new_pos:
            data = self.prog.input[self.pos:new_pos]
            self.buf.append(data)
            self.skip_to(new_pos)

    def move_to_start(self, x: HasSpan) -> None:
        if x.span is None:
            assert isinstance(x, UnaryExpr)
            assert x.op == 'NEW'
            self.move_to_start(x.arg)
            return

        self.move_to(x.span[0].lexpos)

    def move_to_end(self, x: HasSpan) -> None:
        self.move_to(span_endlexpos(x))

    def process(self) -> str:
        assert self.prog.input is not None
        for d in self.prog.decls:
            self.move_to_start(d)
            self.process_decl(d)

        self.move_to(len(self.prog.input))

        return ''.join(self.buf)

    def process_decl(self, d: Decl) -> None:
        assert d.span is not None
        assert self.pos == d.span[0].lexpos

        if isinstance(d, DefinitionDecl) and isinstance(d.body, tuple):
            self.move_and_process_expr(d.expr)
        else:
            self.move_to_end(d)

    def move_and_process_expr(self, e: Expr) -> None:
        self.move_to_start(e)
        self.process_expr(e)

    def process_expr(self, e: Expr) -> None:
        assert e.span is not None or (isinstance(e, UnaryExpr) and e.op == 'NEW')

        if isinstance(e, NaryExpr):
            for arg in e.args:
                self.move_and_process_expr(arg)
            self.move_to_end(e)
        elif isinstance(e, QuantifierExpr):
            self.move_and_process_expr(e.body)
            self.move_to_end(e)
        elif isinstance(e, UnaryExpr):
            if self.ignore_old and e.op == 'OLD':
                assert e.span is not None
                self.skip_to_start(e.arg)
                self.process_expr(e.arg)
                self.move_to(e.span[1].lexpos)  # include whitespace/comments inside close paren
                self.skip_to_end(e)  # *don't* include close paren
                # jrw: test this!
            elif e.op == 'NEW' and e.span is None:
                self.buf.append('new(')
                self.move_and_process_expr(e.arg)
                self.buf.append(')')
            else:
                self.move_and_process_expr(e.arg)
                self.move_to_end(e)
        elif isinstance(e, BinaryExpr):
            self.process_expr(e.arg1)
            self.move_and_process_expr(e.arg2)
        elif isinstance(e, IfThenElse):
            self.move_and_process_expr(e.branch)
            self.move_and_process_expr(e.then)
            self.move_and_process_expr(e.els)
        elif isinstance(e, Let):
            self.move_and_process_expr(e.val)
            self.move_and_process_expr(e.body)
        elif isinstance(e, AppExpr):
            for arg in e.args:
                self.move_and_process_expr(arg)
            self.move_to_end(e)
        elif isinstance(e, (Id, Bool)):
            self.move_to_end(e)
        else:
            assert False, repr(e)

# Use prog.input to print prog as similarly as possible to the input. In particular,
# whitespace and comments are preserved where possible.
#
# If ignore_old is True, then do not print any old() expressions. This is useful
# in conjunction with strip_old=False in translate_old_to_new_prog.
def faithful_print_prog(prog: Program, ignore_old: bool = False) -> str:
    return FaithfulPrinter(prog, ignore_old).process()

@functools.total_ordering
class Expr(Denotable):
    def __init__(self, span: Optional[Span]) -> None:
        super().__init__()
        self.span = span

    def __repr__(self) -> str:
        raise Exception('Unexpected expr %s does not implement __repr__ method' % type(self))

    def __str__(self) -> str:
        buf: List[str] = []
        self.pretty(buf, PREC_TOP, 'NONE')
        return ''.join(buf)

    # typecheck expression and destructively infer types for bound variables.
    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        raise Exception('Unexpected expression %s does not implement resolve method' %
                        repr(self))
    # NOTE(resolving-malformed-programs)
    # mypyvy tries to report as many useful errors as possible about the input program during
    # resolution, by continuing after the point where the first error is detected. This
    # introduces subtleties in the resolver where some invariants are established only assuming
    # no errors have been detected so far. As a rule, if the resolver does not exit/return
    # after detecting an invariant violation, then that invariant should not be relied upon
    # elsewhere in the resolver without first asserting that the program is error free.
    # After the resolver is run, mypyvy exits if any errors are detected, so any other parts
    # of mypyvy can assume all invariants established by the resolver.

    def __lt__(self, other: object) -> bool:
        if not isinstance(other, Expr):
            return NotImplemented
        return self._denote() < other._denote()

    def pretty(self, buf: List[str], prec: int, side: str) -> None:
        needs_parens = not no_parens(self.prec(), prec, side)

        if needs_parens:
            buf.append('(')
            prec = PREC_TOP
            side = 'NONE'

        self._pretty(buf, prec, side)

        if needs_parens:
            buf.append(')')

    def prec(self) -> int:
        raise Exception('Unexpected expr %s does not implement prec method' % repr(self))

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        raise Exception('Unexpected expr %s does not implement pretty method' % repr(self))

    def free_ids(self) -> List[str]:
        raise Exception('Unexpected expr %s does not implement contains_var method' %
                        repr(self))

class Bool(Expr):
    def __init__(self, val: bool, *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        self.val = val

    def __repr__(self) -> str:
        return str(self.val)

    def _denote(self) -> Tuple:
        return (self.val,)

    def prec(self) -> int:
        return PREC_BOT

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        buf.append('true' if self.val else 'false')

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        check_constraint(self.span, sort, BoolSort)
        return BoolSort

    def free_ids(self) -> List[str]:
        return []

TrueExpr  = Bool(True)
FalseExpr = Bool(False)

UNOPS = {
    'NOT',
    'NEW'
}
z3_UNOPS: Dict[str, Optional[Callable[[z3.ExprRef], z3.ExprRef]]] = {
    'NOT': z3.Not,
    'NEW': None
}

def check_constraint(span: Optional[Span], expected: InferenceSort, actual: InferenceSort) -> InferenceSort:
    def normalize(s: Union[Sort, SortInferencePlaceholder]) -> Union[Sort, SortInferencePlaceholder]:
        if isinstance(s, SortInferencePlaceholder):
            s = s.root()
            if s.sort is not None:
                s = s.sort
        return s

    if expected is None or actual is None:
        return expected or actual

    expected = normalize(expected)
    actual = normalize(actual)

    if isinstance(expected, Sort):
        if isinstance(actual, Sort):
            if expected != actual:
                utils.print_error(span, 'expected sort %s but got %s' % (expected, actual))
            return actual  # either would be fine
        else:
            actual.solve(expected)
            return expected
    else:
        if isinstance(actual, Sort):
            expected.solve(actual)
            return actual
        else:
            expected.merge(actual)
            return expected


class UnaryExpr(Expr):
    def __init__(self, op: str, arg: Expr, *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        assert op in UNOPS or op == 'OLD'  # TODO: remove 'OLD'
        self.op = op
        self.arg = arg

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        if self.op == 'NEW':
            if not scope.new_allowed():
                utils.print_error(self.span, f'new is not allowed here because this is a {scope.num_states}-state environment, and the current state index is {scope.current_state_index}')
            with scope.next_state_index():
                return self.arg.resolve(scope, sort)
        elif self.op == 'NOT':
            check_constraint(self.span, sort, BoolSort)
            self.arg.resolve(scope, BoolSort)
            return BoolSort
        elif self.op == 'OLD':
            utils.print_error(self.span, "old() is deprecated and is not supported by the resolver; ignoring...")
            return sort  # bogus
        else:
            assert False

    def _denote(self) -> Tuple:
        return (self.op, self.arg)

    def __repr__(self) -> str:
        return 'UnaryExpr(op=%s, arg=%s)' % (repr(self.op), repr(self.arg))

    def prec(self) -> int:
        if self.op == 'NOT':
            return PREC_NOT
        elif self.op == 'NEW':
            return PREC_BOT
        elif self.op == 'OLD':  # TODO: remove old
            return PREC_BOT
        else:
            assert False

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        if self.op == 'NOT':
            buf.append('!')
            self.arg.pretty(buf, PREC_NOT, 'NONE')
        elif self.op == 'NEW':
            buf.append('new(')
            self.arg.pretty(buf, PREC_TOP, 'NONE')
            buf.append(')')
        elif self.op == 'OLD':  # TODO: remove old
            buf.append('old(')
            self.arg.pretty(buf, PREC_TOP, 'NONE')
            buf.append(')')
        else:
            assert False

    def free_ids(self) -> List[str]:
        return self.arg.free_ids()

def Not(e: Expr) -> Expr:
    return UnaryExpr('NOT', e)

def New(e: Expr) -> Expr:
    return UnaryExpr('NEW', e)

BINOPS = {
    'IMPLIES',
    'IFF',
    'EQUAL',
    'NOTEQ'
}
z3_BINOPS: Dict[str, Callable[[z3.ExprRef, z3.ExprRef], z3.ExprRef]] = {
    'IMPLIES' : z3.Implies,
    'IFF' : lambda x, y: x == y,
    'EQUAL' : lambda x, y: x == y,
    'NOTEQ' : lambda x, y: x != y
}

class BinaryExpr(Expr):
    def __init__(self, op: str, arg1: Expr, arg2: Expr, *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        assert op in BINOPS
        self.op = op
        self.arg1 = arg1
        self.arg2 = arg2

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        check_constraint(self.span, sort, BoolSort)

        if self.op in ['AND', 'OR', 'IMPLIES', 'IFF']:
            self.arg1.resolve(scope, BoolSort)
            self.arg2.resolve(scope, BoolSort)
        else:
            assert self.op in ['EQUAL', 'NOTEQ']
            s = self.arg1.resolve(scope, None)
            self.arg2.resolve(scope, s)

        return BoolSort


    def _denote(self) -> Tuple:
        return (self.op, self.arg1, self.arg2)

    def __repr__(self) -> str:
        return 'BinaryExpr(op=%s, arg1=%s, arg2=%s)' % (
            repr(self.op),
            repr(self.arg1),
            repr(self.arg2))

    def prec(self) -> int:
        if self.op == 'IMPLIES':
            return PREC_IMPLIES
        elif self.op == 'IFF':
            return PREC_IFF
        elif self.op == 'EQUAL' or self.op == 'NOTEQ':
            return PREC_EQ
        else:
            assert False

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        p = self.prec()
        self.arg1.pretty(buf, p, 'LEFT')

        if self.op == 'IMPLIES':
            s = '->'
        elif self.op == 'IFF':
            s = '<->'
        elif self.op == 'EQUAL':
            s = '='
        elif self.op == 'NOTEQ':
            s = '!='
        else:
            assert False

        buf.append(' %s ' % s)

        self.arg2.pretty(buf, p, 'RIGHT')

    def free_ids(self) -> List[str]:
        x = self.arg1.free_ids()
        s = set(x)
        return x + [y for y in self.arg2.free_ids() if y not in s]

NOPS = {
    'AND',
    'OR',
    'DISTINCT'
}

z3_NOPS: Any = {
    'AND': z3.And,
    'OR': z3.Or,
    'DISTINCT': z3.Distinct,
}

class NaryExpr(Expr):
    def __init__(self, op: str, args: List[Expr], *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        assert op in NOPS
        assert len(args) >= 2, (args, span)

        self.op = op
        self.args = args

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        check_constraint(self.span, sort, BoolSort)

        if self.op in ['AND', 'OR']:
            for arg in self.args:
                arg.resolve(scope, BoolSort)
        else:
            assert self.op == 'DISTINCT'
            s: InferenceSort = None
            for arg in self.args:
                s = arg.resolve(scope, s)

        return BoolSort

    def _denote(self) -> Tuple:
        return (self.op, tuple(self.args))

    def __repr__(self) -> str:
        return 'NaryExpr(op=%s, args=%s)' % (repr(self.op), self.args)

    def prec(self) -> int:
        if self.op == 'AND':
            return PREC_AND
        elif self.op == 'OR':
            return PREC_OR
        elif self.op == 'DISTINCT':
            return PREC_BOT
        else:
            assert False

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        assert len(self.args) >= 2

        p = self.prec()

        if self.op == 'AND':
            sep = ' & '
        elif self.op == 'OR':
            sep = ' | '
        elif self.op == 'DISTINCT':
            sep = ', '
        else:
            assert False

        if self.op == 'DISTINCT':
            buf.append('distinct(')

        self.args[0].pretty(buf, p, 'LEFT')

        for arg in self.args[1:-1]:
            buf.append('%s' % sep)
            arg.pretty(buf, p, 'LEFT')

        buf.append('%s' % sep)

        self.args[-1].pretty(buf, p, 'RIGHT')

        if self.op == 'DISTINCT':
            buf.append(')')

    def free_ids(self) -> List[str]:
        l = []
        s: Set[str] = set()

        for arg in self.args:
            for x in arg.free_ids():
                if x not in s:
                    s.add(x)
                    l.append(x)

        return l

def Forall(vs: List[SortedVar], body: Expr) -> Expr:
    if len(vs) == 0:
        return body
    return QuantifierExpr('FORALL', vs, body)

def Exists(vs: List[SortedVar], body: Expr) -> Expr:
    if len(vs) == 0:
        return body
    return QuantifierExpr('EXISTS', vs, body)

def And(*args: Expr) -> Expr:
    if len(args) == 0:
        return TrueExpr
    elif len(args) == 1:
        return args[0]
    else:
        return NaryExpr('AND', list(args))

def Or(*args: Expr) -> Expr:
    if len(args) == 0:
        return FalseExpr
    elif len(args) == 1:
        return args[0]
    else:
        return NaryExpr('OR', list(args))

def Eq(arg1: Expr, arg2: Expr) -> Expr:
    return BinaryExpr('EQUAL', arg1, arg2)

def Neq(arg1: Expr, arg2: Expr) -> Expr:
    return BinaryExpr('NOTEQ', arg1, arg2)

def Iff(arg1: Expr, arg2: Expr) -> Expr:
    return BinaryExpr('IFF', arg1, arg2)

def Implies(arg1: Expr, arg2: Expr) -> Expr:
    return BinaryExpr('IMPLIES', arg1, arg2)

def Apply(callee: str, args: List[Expr]) -> Expr:
    return AppExpr(callee, args)

class AppExpr(Expr):
    def __init__(self, callee: str, args: List[Expr], *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        if not (len(args) > 0):
            utils.print_error(span, "must be applied to at least one argument")
        self.callee = callee
        self.args = args

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        d = scope.get(self.callee)
        if d is None:
            utils.print_error(self.span, 'Unresolved relation or function name %s' % self.callee)
            return sort  # bogus

        if not (isinstance(d, RelationDecl) or isinstance(d, FunctionDecl) or isinstance(d, DefinitionDecl)):
            utils.print_error(self.span, 'Only relations, functions, or definitions can be applied, not %s' % self.callee)
            return sort  # bogus

        if ((isinstance(d, RelationDecl) or isinstance(d, FunctionDecl))
            and d.mutable and not scope.mutable_allowed()):
            name = 'relation' if isinstance(d, RelationDecl) else 'function'
            utils.print_error(self.span, f'Only immutable {name}s can be referenced in this context')
            # note that we don't return here. typechecking can continue.
            # see NOTE(resolving-malformed-programs)

        if isinstance(d, DefinitionDecl) and not scope.call_allowed(d):
            utils.print_error(self.span, f'a {d.num_states}-state definition cannot be called from a {scope.num_states}-state context inside {scope.current_state_index} nested new()s!')

        if len(d.arity) == 0 or len(self.args) != len(d.arity):
            utils.print_error(self.span, 'Callee applied to wrong number of arguments')
        for (arg, s) in zip(self.args, d.arity):
            arg.resolve(scope, s)

        if isinstance(d, RelationDecl):
            check_constraint(self.span, sort, BoolSort)
            return BoolSort
        else:
            sort = check_constraint(self.span, sort, d.sort)
            return sort

    def _denote(self) -> Tuple:
        return (self.callee, tuple(self.args))

    def __repr__(self) -> str:
        return 'AppExpr(rel=%s, args=%s)' % (repr(self.callee), self.args)

    def prec(self) -> int:
        return PREC_BOT

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        buf.append(self.callee)
        buf.append('(')
        started = False
        for arg in self.args:
            if started:
                buf.append(', ')
            started = True
            arg.pretty(buf, PREC_TOP, 'NONE')
        buf.append(')')

    def free_ids(self) -> List[str]:
        l = []
        s: Set[str] = set()
        for arg in self.args:
            for x in arg.free_ids():
                if x not in s:
                    l.append(x)
                    s.add(x)
        return l

class SortedVar(Denotable):
    def __init__(self, name: str, sort: Optional[Sort], *, span: Optional[Span] = None) -> None:
        super().__init__()
        self.span = span
        self.name = name
        self.sort: InferenceSort = sort

    def _denote(self, allow_untyped: bool = False) -> Tuple:
        assert allow_untyped or isinstance(self.sort, Sort), 'SortedVar._denote should only be called after type inference'
        return (self.name, self.sort)

    def __eq__(self, other: object) -> bool:
        return (isinstance(other, SortedVar) and
                type(self) is type(other) and
                self._denote(allow_untyped=True) == other._denote(allow_untyped=True))

    def __hash__(self) -> int:
        return super().__hash__()

    def resolve(self, scope: Scope[InferenceSort]) -> None:
        if self.sort is None:
            utils.print_error(self.span, 'type annotation required for variable %s' % (self.name,))
            return

        assert not isinstance(self.sort, SortInferencePlaceholder)

        self.sort.resolve(scope)

    def __repr__(self) -> str:
        return 'SortedVar(name=%s, sort=%s)' % (repr(self.name), repr(self.sort))

    def __str__(self) -> str:
        if self.sort is None:
            return self.name
        else:
            return '%s:%s' % (self.name, self.sort)

def safe_cast_sort(s: InferenceSort) -> Sort:
    assert isinstance(s, Sort)
    return cast(Sort, s)


class Binder(Denotable):
    def __init__(self, vs: List[SortedVar]) -> None:
        super().__init__()
        self.vs = vs

    def __repr__(self) -> str:
        return 'Binder(%s)' % self.vs

    def _denote(self) -> Tuple:
        return tuple(self.vs)

    def pre_resolve(self, scope: Scope[InferenceSort]) -> None:
        for sv in self.vs:
            if sv.sort is None:
                sv.sort = SortInferencePlaceholder(sv)
            else:
                assert not isinstance(sv.sort, SortInferencePlaceholder)
                sv.sort.resolve(scope)

    def post_resolve(self) -> None:
        for sv in self.vs:
            if isinstance(sv.sort, SortInferencePlaceholder):
                utils.print_error(sv.span, 'Could not infer sort for variable %s' % (sv.name,))


class QuantifierExpr(Expr):
    def __init__(self, quant: str, vs: List[SortedVar], body: Expr, *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        assert quant in ['FORALL', 'EXISTS']
        assert len(vs) > 0

        self.quant = quant
        self.binder = Binder(vs)
        self.body = body

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        check_constraint(self.span, sort, BoolSort)

        self.binder.pre_resolve(scope)

        with scope.in_scope(self.binder, [v.sort for v in self.binder.vs]):
            self.body.resolve(scope, BoolSort)

        self.binder.post_resolve()

        return BoolSort

    def __repr__(self) -> str:
        return 'QuantifierExpr(quant=%s, vs=%s, body=%s)' % (repr(self.quant), self.binder.vs, repr(self.body))

    def _denote(self) -> Tuple:
        return (self.quant, self.binder, self.body)

    def prec(self) -> int:
        return PREC_QUANT

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        buf.append(self.quant.lower())
        buf.append(' ')

        started = False
        for sv in self.binder.vs:
            if started:
                buf.append(', ')
            started = True
            buf.append(str(sv))
        buf.append('. ')

        self.body.pretty(buf, PREC_QUANT, 'NONE')

    def free_ids(self) -> List[str]:
        return [x for x in self.body.free_ids() if not any(v.name == x for v in self.binder.vs)]

    def vs(self) -> List[SortedVar]:
        return self.binder.vs

class Id(Expr):
    '''Unresolved symbol (might represent a constant or a nullary relation or a variable)'''
    def __init__(self, name: str, *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        self.name = name

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        d = scope.get(self.name)

        if d is None:
            utils.print_error(self.span, 'Unresolved variable %s' % (self.name,))
            return sort  # bogus

        if isinstance(d, FunctionDecl):
            utils.print_error(self.span, 'Function %s must be applied to arguments' % (self.name,))
            return sort  # bogus

        if ((isinstance(d, RelationDecl) or isinstance(d, ConstantDecl))
            and d.mutable and not scope.mutable_allowed()):
            name = 'relation' if isinstance(d, RelationDecl) else 'constant'
            utils.print_error(self.span, f'Only immutable {name}s can be referenced in this context')
            return sort  # bogus

        if isinstance(d, RelationDecl):
            if len(d.arity) > 0:
                utils.print_error(self.span, 'Relation %s must be applied to arguments' % (self.name,))
                return sort  # bogus
            check_constraint(self.span, sort, BoolSort)
            return BoolSort
        elif isinstance(d, ConstantDecl):
            sort = check_constraint(self.span, sort, d.sort)
            return sort
        elif isinstance(d, DefinitionDecl):
            if len(d.arity) > 0:
                utils.print_error(self.span, 'Definition %s must be applied to arguments' % (self.name,))
                return sort  # bogus
            check_constraint(self.span, sort, d.sort)
            return BoolSort
        else:
            vsort, = d
            vsort = check_constraint(self.span, sort, vsort)
            return vsort

    def _denote(self) -> Tuple:
        return (self.name,)

    def __repr__(self) -> str:
        return 'Id(name=%s)' % (repr(self.name),)

    def prec(self) -> int:
        return PREC_BOT

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        buf.append(self.name)

    def free_ids(self) -> List[str]:
        return [self.name]

class IfThenElse(Expr):
    def __init__(self, branch: Expr, then: Expr, els: Expr, *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        self.branch = branch
        self.then = then
        self.els = els

    def __repr__(self) -> str:
        return 'IfThenElse(%s, %s, %s)' % (self.branch, self.then, self.els)

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        self.branch.resolve(scope, BoolSort)
        sort = self.then.resolve(scope, sort)
        return self.els.resolve(scope, sort)

    def _denote(self) -> Tuple:
        return (self.branch, self.then, self.els)

    def prec(self) -> int:
        return PREC_TOP

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        buf.append('if ')
        self.branch.pretty(buf, PREC_TOP, 'NONE')
        buf.append(' then ')
        self.then.pretty(buf, PREC_TOP, 'NONE')
        buf.append(' else ')
        self.els.pretty(buf, PREC_TOP, 'NONE')

    def free_ids(self) -> List[str]:
        l1 = self.branch.free_ids()
        s1 = set(l1)
        l2 = [x for x in self.then.free_ids() if x not in s1]
        s2 = set(l2)
        l3 = [x for x in self.els.free_ids() if x not in s1 and x not in s2]
        return l1 + l2 + l3

class Let(Expr):
    def __init__(self, var: SortedVar, val: Expr, body: Expr, *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        self.binder = Binder([var])
        self.val = val
        self.body = body

    def __repr__(self) -> str:
        return 'Let(%s, %s, %s)' % (self.binder, self.val, self.body)

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        self.binder.pre_resolve(scope)

        self.val.resolve(scope, self.binder.vs[0].sort)

        with scope.in_scope(self.binder, [v.sort for v in self.binder.vs]):
            sort = self.body.resolve(scope, sort)

        self.binder.post_resolve()

        return sort

    def _denote(self) -> Tuple:
        return (self.binder, self.val, self.body)

    def prec(self) -> int:
        return PREC_TOP

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        buf.append('let ')
        buf.append(str(self.binder.vs[0]))
        buf.append(' = ')
        self.val.pretty(buf, PREC_TOP, 'NONE')
        buf.append(' in ')
        self.body.pretty(buf, PREC_TOP, 'NONE')

    def free_ids(self) -> List[str]:
        l1 = self.val.free_ids()
        l2 = [x for x in self.body.free_ids() if x != self.binder.vs[0].name]
        return l1 + l2

Arity = List[Sort]

class UninterpretedSort(Sort):
    def __init__(self, name: str, *, span: Optional[Span] = None) -> None:
        super().__init__()
        self.span = span
        self.name = name
        self.decl: Optional[SortDecl] = None

    def resolve(self, scope: Scope) -> None:
        self.decl = scope.get_sort(self.name)
        if self.decl is None:
            utils.print_error(self.span, 'Unresolved sort name %s' % (self.name,))

    def __repr__(self) -> str:
        return 'UninterpretedSort(name=%s)' % (repr(self.name),)

    def __str__(self) -> str:
        return self.name

    def to_z3(self) -> z3.SortRef:
        assert self.decl is not None

        return self.decl.to_z3()

    def _denote(self) -> Tuple:
        return (self.name,)

class _BoolSort(Sort):
    def __repr__(self) -> str:
        return 'bool'

    def __str__(self) -> str:
        return 'bool'

    def resolve(self, scope: Scope) -> None:
        pass

    def to_z3(self) -> z3.SortRef:
        return z3.BoolSort()

    def _denote(self) -> Tuple:
        return ()

def get_decl_from_sort(s: InferenceSort) -> SortDecl:
    assert isinstance(s, UninterpretedSort)
    assert s.decl is not None
    return s.decl

BoolSort = _BoolSort()

class AssumeStatement(object):
    def __init__(self, expr: Expr, *, span: Optional[Span] = None) -> None:
        self.span = span
        self.expr = expr

    def __repr__(self) -> str:
        return 'AssumeStatement(expr=%s)' % self.expr

class AssignmentStatement(object):
    def __init__(self, assignee: str, args: List[Expr], rhs: Expr, *, span: Optional[Span] = None) -> None:
        self.span = span
        self.assignee = assignee
        self.args = args
        self.rhs = rhs

    def __repr__(self) -> str:
        return 'AssignmentStatement(assignee=%s, args=%s, rhs=%s)' % (self.assignee, self.args, self.rhs)

Statement = Union[AssumeStatement, AssignmentStatement]

class BlockStatement(object):
    def __init__(self, stmts: List[Statement], *, span: Optional[Span] = None) -> None:
        self.span = span
        self.stmts = stmts

    def __repr__(self) -> str:
        return 'BlockStatement(stmts=%s)' % self.stmts

def translate_block(block: BlockStatement) -> Tuple[List[ModifiesClause], Expr]:
    mods_str_list: List[str] = []
    conjuncts = []
    for stmt in block.stmts:
        if isinstance(stmt, AssumeStatement):
            conjuncts.append(stmt.expr)
        elif isinstance(stmt, AssignmentStatement):
            assert stmt.assignee not in mods_str_list, 'block statements may only assign to a component once!'
            mods_str_list.append(stmt.assignee)
            if len(stmt.args) == 0:
                conjuncts.append(Eq(New(Id(stmt.assignee)), stmt.rhs))
            else:
                assert isinstance(stmt.rhs, Bool)
                if stmt.rhs.val:
                    f = lambda x, y: Or(x, y)
                else:
                    f = lambda x, y: And(x, Not(y))
                vs = ['X%s' % i for i, _ in enumerate(stmt.args)]
                c = And(*(Eq(Id(X), arg) for X, arg in zip(vs, stmt.args)))

                conjuncts.append(Forall([SortedVar(v, None) for v in vs],
                                        Iff(New(Apply(stmt.assignee, [Id(v) for v in vs])),
                                            f(Apply(stmt.assignee, [Id(v) for v in vs]), c))))
        else:
            reveal_type(stmt)
            assert False
    return ([ModifiesClause(name) for name in mods_str_list], And(*conjuncts))

class Decl(Denotable):
    def __init__(self, span: Optional[Span]) -> None:
        super().__init__()
        self.span = span

    def __repr__(self) -> str:
        raise Exception('Unexpected decl %s does not implement __repr__ method' % type(self))

    def __str__(self) -> str:
        raise Exception('Unexpected decl %s does not implement __str__ method' % type(self))


class SortDecl(Decl):
    def __init__(self, name: str, annotations: List[Annotation], *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        self.span = span
        self.name = name
        self.annotations = annotations
        self.z3: Optional[z3.SortRef] = None

    def __getstate__(self) -> Any:
        return dict(
            super().__getstate__(),
            z3=None,
        )

    def _denote(self) -> Tuple:
        return (self.name,)

    def resolve(self, scope: Scope) -> None:
        scope.add_sort(self)

    def __repr__(self) -> str:
        return 'SortDecl(name=%s)' % (repr(self.name), )

    def __str__(self) -> str:
        return 'sort %s' % self.name

    def to_z3(self) -> z3.SortRef:
        if self.z3 is None:
            self.z3 = z3.DeclareSort(self.name)

        return self.z3

class FunctionDecl(Decl):
    def __init__(self, name: str, arity: Arity, sort: Sort, mutable: bool, annotations: List[Annotation], *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        self.span = span
        self.name = name
        self.arity = arity
        self.sort = sort
        self.mutable = mutable
        self.annotations = annotations
        self.mut_z3: Dict[str, z3.FuncDeclRef] = {}
        self.immut_z3: Optional[z3.FuncDeclRef] = None

        assert len(self.arity) > 0

    def __getstate__(self) -> Any:
        return dict(
            super().__getstate__(),
            mut_z3={},
            immut_z3=None,
        )

    def _denote(self) -> Tuple:
        return (self.name, tuple(self.arity), self.sort, self.mutable)

    def resolve(self, scope: Scope) -> None:
        for sort in self.arity:
            sort.resolve(scope)

        self.sort.resolve(scope)

        scope.add_function(self)

    def __repr__(self) -> str:
        return 'FunctionDecl(name=%s, arity=%s, sort=%s, mutable=%s)' % (
            repr(self.name), self.arity, self.sort, self.mutable
        )

    def __str__(self) -> str:
        return '%s function %s(%s): %s' % (
            'mutable' if self.mutable else 'immutable',
            self.name,
            ', '.join([str(s) for s in self.arity]),
            self.sort
        )

    def to_z3(self, key: Optional[str]) -> z3.FuncDeclRef:
        if self.mutable:
            assert key is not None
            if key not in self.mut_z3:
                a = [s.to_z3() for s in self.arity] + [self.sort.to_z3()]
                self.mut_z3[key] = z3.Function(key + '_' + self.name, *a)

            return self.mut_z3[key]
        else:
            if self.immut_z3 is None:
                a = [s.to_z3() for s in self.arity] + [self.sort.to_z3()]
                self.immut_z3 = z3.Function(self.name, *a)

            return self.immut_z3


class RelationDecl(Decl):
    def __init__(self, name: str, arity: Arity, mutable: bool, derived: Optional[Expr], annotations: List[Annotation], *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        self.span = span
        self.name = name
        self.arity = arity
        self.mutable = mutable
        self.derived_axiom = derived
        self.annotations = annotations
        self.mut_z3: Dict[str, Union[z3.FuncDeclRef, z3.ExprRef]] = {}
        self.immut_z3: Optional[Union[z3.FuncDeclRef, z3.ExprRef]] = None

    def __getstate__(self) -> Any:
        return dict(
            super().__getstate__(),
            mut_z3={},
            immut_z3=None,
        )

    def _denote(self) -> Tuple:
        return (self.name, tuple(self.arity), self.mutable, self.derived_axiom)

    def resolve(self, scope: Scope) -> None:
        for sort in self.arity:
            sort.resolve(scope)

        scope.add_relation(self)

        if self.derived_axiom:
            self.derived_axiom = close_free_vars(self.derived_axiom, span=self.span)
            with scope.n_states(1):
                self.derived_axiom.resolve(scope, BoolSort)

    def __repr__(self) -> str:
        return 'RelationDecl(name=%s, arity=%s, mutable=%s, derived=%s)' % (repr(self.name), self.arity, self.mutable, self.derived_axiom)

    def __str__(self) -> str:
        return '%s relation %s(%s)%s' % ('derived' if self.derived_axiom is not None else
                                         'mutable' if self.mutable else 'immutable',
                                         self.name,
                                         ', '.join([str(s) for s in self.arity]),
                                         '' if not self.derived_axiom
                                         else (': %s' % str(self.derived_axiom)))

    def to_z3(self, key: Optional[str]) -> Union[z3.FuncDeclRef, z3.ExprRef]:
        if self.mutable:
            assert key is not None
            if key not in self.mut_z3:
                if len(self.arity) > 0:
                    a = [s.to_z3() for s in self.arity] + [z3.BoolSort()]
                    self.mut_z3[key] = z3.Function(key + '_' + self.name, *a)
                else:
                    self.mut_z3[key] = z3.Const(key + '_' + self.name, z3.BoolSort())

            return self.mut_z3[key]
        else:
            if self.immut_z3 is None:
                if len(self.arity) > 0:
                    a = [s.to_z3() for s in self.arity] + [z3.BoolSort()]
                    self.immut_z3 = z3.Function(self.name, *a)
                else:
                    self.immut_z3 = z3.Const(self.name, z3.BoolSort())

            return self.immut_z3

    def is_derived(self) -> bool:
        return self.derived_axiom is not None



class ConstantDecl(Decl):
    def __init__(self, name: str, sort: Sort, mutable: bool, annotations: List[Annotation], *, span: Optional[Span]) -> None:
        super().__init__(span)
        self.span = span
        self.name = name
        self.sort = sort
        self.mutable = mutable
        self.annotations = annotations
        self.mut_z3: Dict[str, z3.ExprRef] = {}
        self.immut_z3: Optional[z3.ExprRef] = None

    def __getstate__(self) -> Any:
        return dict(
            super().__getstate__(),
            mut_z3={},
            immut_z3=None,
        )

    def _denote(self) -> Tuple:
        return (self.name, self.sort, self.mutable)

    def __repr__(self) -> str:
        return 'ConstantDecl(name=%s, sort=%s, mutable=%s)' % (repr(self.name), self.sort, self.mutable)

    def __str__(self) -> str:
        return '%s constant %s: %s' % ('mutable' if self.mutable else 'immutable',
                                       self.name, self.sort)

    def resolve(self, scope: Scope) -> None:
        self.sort.resolve(scope)
        scope.add_constant(self)

    def to_z3(self, key: Optional[str]) -> z3.ExprRef:
        if self.mutable:
            assert key is not None
            if key not in self.mut_z3:
                self.mut_z3[key] = z3.Const(key + '_' + self.name, self.sort.to_z3())

            return self.mut_z3[key]
        else:
            if self.immut_z3 is None:
                self.immut_z3 = z3.Const(self.name, self.sort.to_z3())

            return self.immut_z3

def close_free_vars(expr: Expr, in_scope: List[str]=[], span: Optional[Span] = None) -> Expr:
    vs = [s for s in expr.free_ids() if s not in in_scope and s.isupper()]
    if vs == []:
        return expr
    else:
        return QuantifierExpr('FORALL', [SortedVar(v, None, span=span) for v in vs], expr, span=span)

class InitDecl(Decl):
    def __init__(self, name: Optional[str], expr: Expr, *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        self.span = span
        self.name = name
        self.expr = expr

    def _denote(self) -> Tuple:
        return (self.name, self.expr)

    def resolve(self, scope: Scope) -> None:
        self.expr = close_free_vars(self.expr, span=self.span)
        with scope.n_states(1):
            self.expr.resolve(scope, BoolSort)

        if symbols_used(scope, self.expr) == set():
            utils.print_error(self.span, 'this initial condition mentions no mutable symbols. it should be declared `axiom` instead.')

    def __repr__(self) -> str:
        return 'InitDecl(name=%s, expr=%s)' % (
            repr(self.name) if self.name is not None else 'None',
            repr(self.expr))

    def __str__(self) -> str:
        return 'init %s%s' % (('[%s] ' % self.name) if self.name is not None else '',
                              self.expr)

class ModifiesClause(object):
    def __init__(self, name: str, *, span: Optional[Span] = None) -> None:
        self.span = span
        self.name = name

    def resolve(self, scope: Scope[InferenceSort]) -> None:
        d = scope.get(self.name)
        assert d is None or isinstance(d, RelationDecl) or \
            isinstance(d, ConstantDecl) or isinstance(d, FunctionDecl)
        if d is None:
            utils.print_error(self.span, 'Unresolved constant, relation, or function %s' % (self.name,))

    def __repr__(self) -> str:
        return 'ModifiesClause(name=%s)' % (repr(self.name),)

    def __str__(self) -> str:
        return self.name

def uses_new(e: Expr) -> bool:
    if isinstance(e, Bool):
        return False
    elif isinstance(e, UnaryExpr):
        return e.op == 'NEW' or uses_new(e.arg)
    elif isinstance(e, BinaryExpr):
        return uses_new(e.arg1) or uses_new(e.arg2)
    elif isinstance(e, NaryExpr):
        return any(uses_new(x) for x in e.args)
    elif isinstance(e, AppExpr):
        return any(uses_new(x) for x in e.args)
    elif isinstance(e, QuantifierExpr):
        return uses_new(e.body)
    elif isinstance(e, Id):
        return False
    elif isinstance(e, IfThenElse):
        return uses_new(e.branch) or uses_new(e.then) or uses_new(e.els)
    elif isinstance(e, Let):
        return uses_new(e.val) or uses_new(e.body)
    else:
        assert False, e

def uses_old(e: Expr) -> bool:
    if isinstance(e, Bool):
        return False
    elif isinstance(e, UnaryExpr):
        return e.op == 'OLD' or uses_old(e.arg)
    elif isinstance(e, BinaryExpr):
        return uses_old(e.arg1) or uses_old(e.arg2)
    elif isinstance(e, NaryExpr):
        return any(uses_old(x) for x in e.args)
    elif isinstance(e, AppExpr):
        return any(uses_old(x) for x in e.args)
    elif isinstance(e, QuantifierExpr):
        return uses_old(e.body)
    elif isinstance(e, Id):
        return False
    elif isinstance(e, IfThenElse):
        return uses_old(e.branch) or uses_old(e.then) or uses_old(e.els)
    elif isinstance(e, Let):
        return uses_old(e.val) or uses_old(e.body)
    else:
        assert False, e

class OldToNewTranslator(object):
    def __init__(self, scope: Scope, strip_old: bool = True) -> None:
        self.scope = scope
        self.strip_old = strip_old

        self.in_old = False
        self.out_new = False
        self.mutable_callee: Optional[Span] = None

    @contextmanager
    def set_in_old(self) -> Iterator[None]:
        assert not self.in_old
        self.in_old = True
        yield None
        self.in_old = False

    @contextmanager
    def set_out_new(self) -> Iterator[None]:
        assert not self.out_new
        self.out_new = True
        yield None
        self.out_new = False

    @contextmanager
    def set_mutable_callee(self, span: Optional[Span]) -> Iterator[None]:
        old_val = self.mutable_callee
        self.mutable_callee = span
        yield None
        self.mutable_callee = old_val

    def translate(self, e: Expr) -> Expr:
        assert not (self.in_old and self.out_new)

        if isinstance(e, Bool):
            return e
        elif isinstance(e, UnaryExpr):
            if e.op == 'OLD':
                if self.out_new:
                    err_msg = ('this use of old() is nested within a reference to a mutable '
                               'symbol in the new state. the old-to-new translator does not '
                               'currently support this case. please lift the use of old() above '
                               'the mutable reference using a let expression and try again.')
                    utils.print_error(e.span, err_msg)
                    if self.mutable_callee is not None:
                        info_msg = 'here is the mutable symbol reference in the new state.'
                        utils.print_info(self.mutable_callee, info_msg)
                    # bogus return value, just keep going to potentially report more errors
                    # see NOTE(resolving-malformed-programs)
                    return UnaryExpr(e.op, self.translate(e.arg), span=e.span)
                else:
                    with self.set_in_old():
                        if self.strip_old:
                            return self.translate(e.arg)
                        else:
                            return UnaryExpr(e.op, self.translate(e.arg), span=e.span)
            elif e.op == 'NEW':
                err_msg = 'old-to-new translator does not support mixing calls to new and old!'
                utils.print_error(e.span, err_msg)
                # bogus return value, just keep going to potentially report more errors
                # see NOTE(resolving-malformed-programs)
                return UnaryExpr(e.op, self.translate(e.arg), span=e.span)
            elif e.op == 'NOT':
                return UnaryExpr(e.op, self.translate(e.arg), span=e.span)
            else:
                assert False, (e.op, e)
        elif isinstance(e, BinaryExpr):
            return BinaryExpr(e.op, self.translate(e.arg1), self.translate(e.arg2), span=e.span)
        elif isinstance(e, NaryExpr):
            return NaryExpr(e.op, [self.translate(arg) for arg in e.args], span=e.span)
        elif isinstance(e, AppExpr):
            d = self.scope.get(e.callee)
            assert d is not None
            if isinstance(d, (RelationDecl, FunctionDecl)) and d.mutable and not self.in_old and not self.out_new:
                with self.set_out_new():
                    with self.set_mutable_callee(e.span):
                        t_args = [self.translate(arg) for arg in e.args]
                        return New(AppExpr(e.callee, t_args, span=e.span))
            else:
                t_args = [self.translate(arg) for arg in e.args]
                return AppExpr(e.callee, t_args, span=e.span)
        elif isinstance(e, QuantifierExpr):
            with self.scope.in_scope(e.binder, [v.sort for v in e.binder.vs]):
                return QuantifierExpr(e.quant, e.binder.vs, self.translate(e.body), span=e.span)
        elif isinstance(e, Id):
            d = self.scope.get(e.name)
            if isinstance(d, (RelationDecl, ConstantDecl)) and d.mutable and not self.in_old and not self.out_new:
                return New(Id(e.name, span=e.span))
            else:
                return e
        elif isinstance(e, IfThenElse):
            return IfThenElse(
                self.translate(e.branch),
                self.translate(e.then),
                self.translate(e.els),
                span=e.span)
        elif isinstance(e, Let):
            with self.scope.in_scope(e.binder, [v.sort for v in e.binder.vs]):
                return Let(e.binder.vs[0],
                           self.translate(e.val),
                           self.translate(e.body),
                           span=e.span)
        else:
            assert False, e

def translate_old_to_new_expr(scope: Scope, e: Expr, strip_old: bool = True) -> Expr:
    return OldToNewTranslator(scope, strip_old=strip_old).translate(e)

# Translate all double-vocabulary formulas in prog from old() syntax to new() syntax.
# If strip_old is False, then leave the old() expressions in place, but also introduce
# new() expressions. (This is useful if the consumer plans to manually ignore old(),
# but wishes to retain source-level information on where old() operations used to be.)
def translate_old_to_new_prog(prog: Program, strip_old: bool = True) -> Program:
    scope = prog.scope
    ds: List[Decl] = []
    for d in prog.decls:
        if isinstance(d, DefinitionDecl) and d.num_states == 2:
            if not uses_old(d.expr) and not uses_new(d.expr):
                utils.print_error(d.span, 'twostate expression uses neither old() nor new(); cannot automatically detect whether it needs refactoring')
            if uses_old(d.expr):
                dd = copy(d)
                with scope.in_scope(d.binder, [v.sort for v in d.binder.vs]):
                    dd.expr = translate_old_to_new_expr(scope, dd.expr, strip_old=strip_old)
                ds.append(dd)
            else:
                ds.append(d)
        elif isinstance(d, TheoremDecl) and d.num_states == 2:
            if not uses_old(d.expr) and not uses_new(d.expr):
                utils.print_error(d.span, 'twostate expression uses neither old() nor new(); cannot automatically detect whether it needs refactoring')
            if uses_old(d.expr):
                t = copy(d)
                t.expr = translate_old_to_new_expr(scope, t.expr, strip_old=strip_old)
                ds.append(t)
            else:
                ds.append(d)
        else:
            ds.append(d)
    new_prog = Program(ds)
    new_prog.input = prog.input
    return new_prog

class DefinitionDecl(Decl):
    def __init__(self, is_public_transition: bool, num_states: int,
                 name: str, params: List[SortedVar],
                 body: Union[BlockStatement, Tuple[List[ModifiesClause], Expr]],
                 *, span: Optional[Span] = None) -> None:
        def implies(a: bool, b: bool) -> bool:
            return not a or b
        # these asserts are enforced by the parser
        assert num_states in (0, 1, 2)
        assert implies(is_public_transition, num_states == 2)
        assert isinstance(body, BlockStatement) or len(body[0]) == 0 or num_states == 2

        super().__init__(span)
        self.span = span
        self.is_public_transition = is_public_transition
        self.num_states = num_states
        self.name = name
        self.binder = Binder(params)
        self.arity = [sv.sort for sv in params]
        self.sort = BoolSort
        self.body = body
        if isinstance(self.body, BlockStatement):
            self.mods, self.expr = translate_block(self.body)
        else:
            self.mods, self.expr = self.body

    def _denote(self) -> Tuple:
        return (self.is_public_transition, self.num_states, self.name, self.binder, self.body)

    def resolve(self, scope: Scope) -> None:
        assert len(scope.stack) == 0

        old_error_count = 0

        self.binder.pre_resolve(scope)

        for mod in self.mods:
            mod.resolve(scope)

        if self.num_states == 2:
            if not uses_old(self.expr) and not uses_new(self.expr):
                utils.print_error(self.span, 'twostate expression uses neither old() nor new(); cannot automatically detect whether it needs to be translated')

            if uses_old(self.expr):
                if utils.args.accept_old:
                    utils.print_warning(self.span, 'old() is deprecated; please use new(). as a temporary convenience, mypyvy will now attempt to automatically translate from old() to new()...')

                    utils.logger.info(f'translating transition {self.name}')
                    with scope.in_scope(self.binder, [v.sort for v in self.binder.vs]):
                        self.expr = translate_old_to_new_expr(scope, self.expr)
                else:
                    utils.print_error(self.span, 'old() is disallowed by --no-accept-old')

        self.expr = close_free_vars(self.expr, in_scope=[v.name for v in self.binder.vs], span=self.span,)

        with scope.in_scope(self.binder, [v.sort for v in self.binder.vs]):
            with scope.n_states(self.num_states):
                self.expr.resolve(scope, BoolSort)

        self.binder.post_resolve()

        if utils.error_count > old_error_count:
            return

        if self.num_states == 2:
            with scope.in_scope(self.binder, [v.sort for v in self.binder.vs]):
                syms = symbols_used(scope, self.expr)
                for index, spans, sym in syms:
                    if index == 1:
                        for mod in self.mods:
                            if mod.name == sym:
                                break
                        else:
                            decl = scope.get(sym)
                            assert decl is not None
                            if not (isinstance(decl, RelationDecl) and decl.is_derived()):
                                if len(spans) == 1:
                                    utils.print_error(spans[0], 'symbol %s is referred to in the new state, but is not mentioned in the modifies clause' % (sym,))
                                else:
                                    utils.print_error(spans[0], 'this call indirectly refers to symbol %s in the new state, but is not mentioned in the modifies clause' % (sym,))
                                    for span in spans[1:-1]:
                                        utils.print_info(span, 'symbol %s is referred to via a call-chain passing through this point' % (sym,))
                                    utils.print_info(spans[-1], 'symbol %s is referred to here' % (sym,))

                for mod in self.mods:
                    decl = scope.get(mod.name)
                    assert decl is not None
                    if isinstance(decl, RelationDecl) and decl.is_derived():
                        utils.print_error(mod.span, 'derived relation %s may not be mentioned by the modifies clause, since derived relations are always modified' % (mod.name,))
                        continue
                    for index, _, sym in syms:
                        if mod.name == sym and index == 1:
                            break
                    else:
                        utils.print_error(mod.span, 'symbol %s is mentioned by the modifies clause, but is not referred to in the new state, so it will be havoced. supress this error by using %s in a no-op.' % (mod.name, mod.name))

    def __repr__(self) -> str:
        return 'TransitionDecl(name=%s, params=%s, mods=%s, expr=%s)' % (
            repr(self.name),
            self.binder.vs,
            self.mods, repr(self.expr))

    def __str__(self) -> str:
        return 'transition %s(%s)\n  modifies %s\n  %s' % \
            (self.name,
             ', '.join([str(v) for v in self.binder.vs]),
             ', '.join([str(m) for m in self.mods]),
             self.expr)

class InvariantDecl(Decl):
    def __init__(self, name: Optional[str], expr: Expr, is_safety: bool, is_sketch: bool, *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        self.span = span
        self.name = name
        self.expr = expr
        self.is_safety = is_safety
        self.is_sketch = is_sketch

    def _denote(self) -> Tuple:
        return (self.name, self.expr)

    def resolve(self, scope: Scope) -> None:
        self.expr = close_free_vars(self.expr, span=self.span)
        with scope.n_states(1):
            self.expr.resolve(scope, BoolSort)

        if not scope.in_phase_context and symbols_used(scope, self.expr) == set():
            utils.print_error(self.span, 'this invariant mentions no mutable symbols. it can be deleted.')

    def __repr__(self) -> str:
        return 'InvariantDecl(name=%s, expr=%s, is_safety=%s, is_sketch=%s)' % (
            repr(self.name) if self.name is not None else 'None',
            repr(self.expr),
            repr(self.is_safety),
            repr(self.is_sketch)
        )

    def __str__(self) -> str:
        kwd = 'safety' if self.is_safety else 'invariant'
        pre = '' if not self.is_sketch else 'sketch '
        return '%s %s%s' % (pre + kwd,
                            ('[%s] ' % self.name) if self.name is not None else '',
                            self.expr)


class AxiomDecl(Decl):
    def __init__(self, name: Optional[str], expr: Expr, *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        self.span = span
        self.name = name
        self.expr = expr

    def _denote(self) -> Tuple:
        return (self.name, self.expr)

    def resolve(self, scope: Scope) -> None:
        self.expr = close_free_vars(self.expr, span=self.span)
        self.expr.resolve(scope, BoolSort)

    def __repr__(self) -> str:
        return 'AxiomDecl(name=%s, expr=%s)' % (
            repr(self.name) if self.name is not None else 'None',
            repr(self.expr))

    def __str__(self) -> str:
        return 'axiom %s%s' % (('[%s] ' % self.name) if self.name is not None else '',
                               self.expr)

class TheoremDecl(Decl):
    def __init__(self, name: Optional[str], expr: Expr, num_states: int, *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        assert num_states in (0, 1, 2)  # enforced by parser
        self.span = span
        self.name = name
        self.expr = expr
        self.num_states = num_states

    def _denote(self) -> Tuple:
        return (self.name, self.expr, self.num_states)

    def resolve(self, scope: Scope) -> None:
        if self.num_states == 2:
            if not uses_old(self.expr) and not uses_new(self.expr):
                utils.print_error(self.span, 'twostate expression uses neither old() nor new(); cannot automatically detect whether it needs to be translated')

            if uses_old(self.expr):
                if utils.args.accept_old:
                    utils.print_warning(self.span, 'old() is deprecated; please use new(). as a temporary convenience, mypyvy will now attempt to automatically translate from old() to new()...')

                    utils.logger.info(f'translating theorem {self.name}')
                    self.expr = translate_old_to_new_expr(scope, self.expr)
                else:
                    utils.print_error(self.span, 'old() is disallowed by --no-accept-old')

        self.expr = close_free_vars(self.expr, span=self.span)
        with scope.n_states(self.num_states):
            self.expr.resolve(scope, BoolSort)

    def __repr__(self) -> str:
        return 'TheoremDecl(name=%s, expr=%s, num_states=%s)' % (
            repr(self.name) if self.name is not None else 'None',
            repr(self.expr),
            self.num_states
        )

    def __str__(self) -> str:
        return '%stheorem %s%s' % (
            'twostate ' if self.num_states == 2 else
            'zerostate ' if self.num_states == 0 else '',
            ('[%s] ' % self.name) if self.name is not None else '',
            self.expr
        )

## decls inside an automaton block

class PhaseTransitionDecl(Denotable):
    def __init__(self, transition: str, precond: Optional[Expr], target: Optional[str], *, span: Optional[Span] = None) -> None:
        self.span = span
        self.transition = transition
        self.precond = precond
        self.target = target

    def _denote(self) -> Tuple:
        return (self.transition, self.precond, self.target)

    def __repr__(self) -> str:
        return 'PhaseTransitionDecl(transition=%s, target=%s, precond=%s)' % (
            repr(self.transition),
            repr(self.target),
            repr(self.precond),
        )

    def __str__(self) -> str:
        return 'transition %s -> %s %s' % (
            self.transition,
            self.target,
            (('assume %s' % self.precond) if (self.precond is not None) else ''),
        )

    def resolve(self, scope: Scope) -> None:
        transition = scope.get_definition(self.transition)
        if transition is None:
            utils.print_error(self.span, 'unknown transition %s' % (self.transition,))
            return

        if self.precond is not None:
            transition_constants = transition.binder.vs
            self.precond = close_free_vars(self.precond, in_scope=[x.name for x in transition_constants], span=self.span)
            with scope.in_scope(transition.binder, [v.sort for v in transition_constants]):
                with scope.n_states(1):
                    self.precond.resolve(scope, BoolSort)

        if self.target is not None and scope.get_phase(self.target) is None:
            utils.print_error(self.span, 'unknown phase %s' % (self.target))

PhaseComponent = Union[PhaseTransitionDecl, InvariantDecl]

class GlobalPhaseDecl(Denotable):
    def __init__(self, components: Sequence[PhaseComponent], *, span: Optional[Span] = None) -> None:
        self.span = span
        self.components = components

    def _denote(self) -> Tuple:
        return tuple(self.components)

    def __repr__(self) -> str:
        return 'GlobalPhaseDecl(components=%s)' % (
            repr(self.components),
        )

    def __str__(self) -> str:
        msg = ''
        for c in self.components:
            msg += '\n  '
            msg += str(c)

        return 'global%s' % (
            msg,
        )

    def resolve(self, scope: Scope) -> None:
        for c in self.components:
            c.resolve(scope)

class InitPhaseDecl(Denotable):
    def __init__(self, phase: str, *, span: Optional[Span] = None) -> None:
        self.span = span
        self.phase = phase

    def _denote(self) -> Tuple:
        return (self.phase,)

    def __repr__(self) -> str:
        return 'InitPhaseDecl(phase=%s)' % (
            self.phase,
        )

    def __str__(self) -> str:
        return 'init phase %s' % (
            self.phase,
        )

    def resolve(self, scope: Scope) -> None:
        if scope.get_phase(self.phase) is None:
            utils.print_error(self.span, 'unknown phase %s' % (self.phase,))


class PhaseDecl(Denotable):
    def __init__(self, name: str, components: Sequence[PhaseComponent], *, span: Optional[Span] = None) -> None:
        self.span = span
        self.name = name
        self.components = components

    def _denote(self) -> Tuple:
        return (self.name, tuple(self.components))

    def __repr__(self) -> str:
        return 'PhaseDecl(name=%s, components=%s)' % (
            repr(self.name),
            repr(self.components),
        )

    def __str__(self) -> str:
        msg = ''
        for c in self.components:
            msg += '\n  '
            msg += str(c)

        return 'phase %s%s' % (
            self.name,
            msg,
        )

    def resolve(self, scope: Scope) -> None:
        with scope.in_phase():
            for c in self.components:
                c.resolve(scope)

    def invs(self) -> Iterator[InvariantDecl]:
        for c in self.components:
            if isinstance(c, InvariantDecl):
                yield c

    def safeties(self) -> Iterator[InvariantDecl]:
        for c in self.components:
            if isinstance(c, InvariantDecl) and c.is_safety :
                yield c

    def sketch_invs(self) -> Iterator[InvariantDecl]:
        for c in self.components:
            if isinstance(c, InvariantDecl) and c.is_sketch:
                yield c


    def transitions(self) -> Iterator[PhaseTransitionDecl]:
        for c in self.components:
            if isinstance(c, PhaseTransitionDecl):
                yield c


AutomatonComponent = Union[GlobalPhaseDecl, InitPhaseDecl, PhaseDecl]

class AutomatonDecl(Decl):
    def __init__(self, components: Sequence[AutomatonComponent], *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        self.span = span
        self.components = components

    def _denote(self) -> Tuple:
        return tuple(self.components)

    def inits(self) -> Iterator[InitPhaseDecl]:
        for c in self.components:
            if isinstance(c, InitPhaseDecl):
                yield c

    def the_init(self) -> Optional[InitPhaseDecl]:
        i = list(self.inits())
        if len(i) == 0:
            utils.print_error(self.span, 'automaton must declare an initial phase')
            return None
        elif len(i) > 1:
            utils.print_error(self.span, 'automaton may only declare one initial phase')

        return i[0]

    def globals(self) -> Iterator[GlobalPhaseDecl]:
        for c in self.components:
            if isinstance(c, GlobalPhaseDecl):
                yield c

    def phases(self) -> Iterator[PhaseDecl]:
        for c in self.components:
            if isinstance(c, PhaseDecl):
                yield c

    def resolve(self, scope: Scope) -> None:
        for p in self.phases():
            scope.add_phase(p)

        gs = list(self.globals())
        gcs: List[PhaseComponent] = []
        for g in gs:
            g.resolve(scope)
            gcs.extend(g.components)

        for p in self.phases():
            p.components = list(p.components) + gcs
            p.resolve(scope)

        init_phase = self.the_init()

        if init_phase is None:
            return  # error reported already from the_init()

        init_phase.resolve(scope)

    def __repr__(self) -> str:
        return 'AutomatonDecl(components=%s)' % (
            self.components
        )

    def __str__(self) -> str:
        msg = ''
        started = False
        for c in self.components:
            msg += '\n'
            started = True
            msg += str(c)

        if started:
            msg += '\n'

        return 'automaton {%s}' % (
            msg
        )

class AnyTransition(Denotable):
    def _denote(self) -> Tuple:
        return ()

    def __str__(self) -> str:
        return 'any transition'

    def resolve(self, scope: Scope) -> None:
        pass

class Star(Denotable):
    def _denote(self) -> Tuple:
        return ()

    def __str__(self) -> str:
        return '*'

class TransitionCall(Denotable):
    def __init__(self, target: str, args: Optional[List[Union[Star, Expr]]], *, span: Optional[Span] = None) -> None:
        super().__init__()
        self.span = span
        self.target = target
        self.args = args

    def _denote(self) -> Tuple:
        return (self.target, self.args)

    def __str__(self) -> str:
        return '%s%s' % (
            self.target,
            '' if self.args is None
            else '(%s)' % ', '.join(str(a) for a in self.args)
        )

    def resolve(self, scope: Scope) -> None:
        ition = scope.get_definition(self.target)
        if ition is None:
            utils.print_error(self.span, 'could not find transition %s' % (self.target,))
            return

        if self.args is not None:
            if len(self.args) != len(ition.binder.vs):
                utils.print_error(self.span, 'transition applied to the wrong number of arguments (expected %s, got %s)' % (len(ition.binder.vs), len(self.args)))
                return

            for a, sort in zip(self.args, (v.sort for v in ition.binder.vs)):
                if isinstance(a, Expr):
                    with scope.n_states(1):
                        a.resolve(scope, sort)

class TransitionCalls(Denotable):
    def __init__(self, calls: List[TransitionCall]) -> None:
        super().__init__()
        self.calls = calls

    def _denote(self) -> Tuple:
        return tuple(self.calls)

    def __str__(self) -> str:
        return ' | '.join(str(c) for c in self.calls)

    def resolve(self, scope: Scope) -> None:
        for c in self.calls:
            c.resolve(scope)

TransitionExpr = Union[AnyTransition, TransitionCalls]

class TraceTransitionDecl(Denotable):
    def __init__(self, transition: TransitionExpr) -> None:
        super().__init__()
        self.transition = transition

    def _denote(self) -> Tuple:
        return (self.transition,)

    def __str__(self) -> str:
        return str(self.transition)

    def resolve(self, scope: Scope) -> None:
        self.transition.resolve(scope)


class AssertDecl(Denotable):
    # expr may only be None in first step, where it means "init"
    def __init__(self, expr: Optional[Expr], *, span: Optional[Span] = None) -> None:
        super().__init__()
        self.span = span
        self.expr = expr

    def _denote(self) -> Tuple:
        return (self.expr, )

    def __str__(self) -> str:
        return 'assert %s' % (str(self.expr),)

    def resolve(self, scope: Scope) -> None:
        if self.expr is not None:
            self.expr = close_free_vars(self.expr, span=self.span)
            with scope.n_states(1):
                self.expr.resolve(scope, BoolSort)


TraceComponent = Union[TraceTransitionDecl, AssertDecl] # , AxiomDecl, ConstantDecl]

class TraceDecl(Decl):
    def __init__(self, components: List[TraceComponent], sat: bool, *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        self.span = span
        self.components = components
        self.sat = sat

    def _denote(self) -> Tuple:
        return (tuple(self.components), self.sat)

    def __str__(self) -> str:
        return 'trace {%s\n}' % (
            '\n  '.join([''] + [str(c) for c in self.components])
        )

    def transitions(self) -> Iterator[TraceTransitionDecl]:
        for c in self.components:
            if isinstance(c, TraceTransitionDecl):
                yield c

    def resolve(self, scope: Scope) -> None:
        for c in self.components:
            c.resolve(scope)

@dataclass
class Annotation(object):
    span: Optional[Span]
    name: str
    args: List[str]

class HasAnnotations(Protocol):
    annotations: List[Annotation]

def has_annotation(d: HasAnnotations, name: str) -> bool:
    return any(annot.name == name for annot in d.annotations)

def get_annotation(d: HasAnnotations, name: str) -> Optional[Annotation]:
    for annot in d.annotations:
        if annot.name == name:
            return annot

    return None

class Scope(Generic[B]):
    def __init__(self) -> None:
        self.stack: List[List[Tuple[str, B]]] = []
        self.sorts: Dict[str, SortDecl] = {}
        self.relations: Dict[str, RelationDecl] = {}
        self.constants: Dict[str, ConstantDecl] = {}
        self.functions: Dict[str, FunctionDecl] = {}
        self.definitions: Dict[str, DefinitionDecl] = {}
        self.phases: Dict[str, PhaseDecl] = {}

        # invariant: num_states > 0 ==> current_state_index < num_states
        self.num_states: int = 0
        self.current_state_index: int = 0

        self.in_phase_context = False

    def new_allowed(self) -> bool:
        return self.current_state_index + 1 < self.num_states

    def mutable_allowed(self) -> bool:
        return self.num_states > 0

    # NOTE(calling-stateful-definitions)
    # A twostate definition cannot be called from a twostate context inside of a new(), since
    # by that point we are in the "next" state. In general, when calling a k-state definition,
    # the following must hold:
    #     current_state_index + (k - 1) < num_states
    # Also note that this correctly handles the case of calling a 0-state definition from a
    # 0-state context, since then current_state_index = 0 and num_states = 0, and -1 < 0.
    def call_allowed(self, d: DefinitionDecl) -> bool:
        return self.current_state_index + (d.num_states - 1) < self.num_states

    def push(self, l: List[Tuple[str, B]]) -> None:
        self.stack.append(l)

    def pop(self) -> None:
        self.stack.pop()

    def get(self, name: str) -> Union[DefinitionDecl, RelationDecl, ConstantDecl, FunctionDecl, Tuple[B], None]:
        # first, check for bound variables in scope
        for l in reversed(self.stack):
            for v, b in l:
                if v == name:
                    return (b,)

        # otherwise, check for constants/relations/functions/definitions (whose domains are disjoint)
        d = self.constants.get(name) or self.relations.get(name) or self.functions.get(name) or self.definitions.get(name)
        return d

    def _check_duplicate_name(self, span: Optional[Span], name: str) -> None:
        if name in self.constants:
            utils.print_error(span, 'Name %s is already declared as a constant' % (name,))

        if name in self.relations:
            utils.print_error(span, 'Name %s is already declared as a relation' % (name,))

        if name in self.functions:
            utils.print_error(span, 'Name %s is already declared as a function' % (name,))

        if name in self.definitions:
            utils.print_error(span, 'Name %s is already declared as a definition' % (name,))


    def add_sort(self, decl: SortDecl) -> None:
        assert len(self.stack) == 0

        span = decl.span
        sort = decl.name

        if sort in self.sorts:
            utils.print_error(span, 'Duplicate sort name %s' % (sort,))

        self.sorts[sort] = decl

    def get_sort(self, sort: str) -> Optional[SortDecl]:
        return self.sorts.get(sort)

    def get_sort_checked(self, sort: str) -> SortDecl:
        res = self.get_sort(sort)
        assert res is not None
        return res

    def add_constant(self, decl: ConstantDecl) -> None:
        assert len(self.stack) == 0

        self._check_duplicate_name(decl.span, decl.name)
        self.constants[decl.name] = decl

    def add_relation(self, decl: RelationDecl) -> None:
        assert len(self.stack) == 0

        self._check_duplicate_name(decl.span, decl.name)
        self.relations[decl.name] = decl

    def get_relation(self, relname: str) -> Optional[RelationDecl]:
        return self.relations.get(relname)

    def add_function(self, decl: FunctionDecl) -> None:
        assert len(self.stack) == 0

        self._check_duplicate_name(decl.span, decl.name)
        self.functions[decl.name] = decl

    def add_phase(self, decl: PhaseDecl) -> None:
        assert len(self.stack) == 0

        if decl.name is not None:
            if decl.name in self.phases:
                utils.print_error(decl.span, 'there is already a phase named %s' % decl.name)
            self.phases[decl.name] = decl

    def get_phase(self, phase: str) -> Optional[PhaseDecl]:
        return self.phases.get(phase)

    def add_definition(self, decl: DefinitionDecl) -> None:
        assert len(self.stack) == 0

        self._check_duplicate_name(decl.span, decl.name)
        self.definitions[decl.name] = decl

    def get_definition(self, definition: str) -> Optional[DefinitionDecl]:
        return self.definitions.get(definition)

    @contextmanager
    def fresh_stack(self) -> Iterator[None]:
        stack = self.stack
        self.stack = []
        yield None
        assert self.stack == []
        self.stack = stack

    @contextmanager
    def next_state_index(self) -> Iterator[None]:
        previous = self.current_state_index
        if self.current_state_index + 1 < self.num_states:
            self.current_state_index += 1
            yield None
            self.current_state_index -= 1
        else:
            assert utils.error_count > 0
            yield None

    @contextmanager
    def n_states(self, n: int) -> Iterator[None]:
        assert n >= 0
        assert self.num_states == 0 and self.current_state_index == 0
        self.num_states = n
        self.current_state_index = 0
        yield None
        self.num_states = 0
        self.current_state_index = 0

    @contextmanager
    def in_phase(self) -> Iterator[None]:
        assert not self.in_phase_context
        self.in_phase_context = True
        yield None
        assert self.in_phase_context
        self.in_phase_context = False

    @contextmanager
    def in_scope(self, b: Binder, annots: List[B]) -> Iterator[None]:
        n = len(self.stack)
        assert len(b.vs) == len(annots)
        self.push(list(zip((v.name for v in b.vs), annots)))
        yield
        self.pop()
        assert n == len(self.stack)

    def fresh(self, base_name: str, also_avoid: List[str]=[]) -> str:
        if self.get(base_name) is None:
            return base_name
        counter = 0
        candidate = base_name + str(counter)
        while self.get(candidate) is not None or candidate in also_avoid:
            counter += 1
            candidate = base_name + str(counter)
        return candidate

StateDecl = Union[RelationDecl, ConstantDecl, FunctionDecl]

class Program(object):
    def __init__(self, decls: List[Decl]) -> None:
        self.decls = decls
        self.scope: Scope[InferenceSort]
        self.input: Optional[str] = None

    def sorts(self) -> Iterator[SortDecl]:
        for d in self.decls:
            if isinstance(d, SortDecl):
                yield d

    def inits(self) -> Iterator[InitDecl]:
        for d in self.decls:
            if isinstance(d, InitDecl):
                yield d

    def invs(self) -> Iterator[InvariantDecl]:
        for d in self.decls:
            if isinstance(d, InvariantDecl):
                yield d

    def safeties(self) -> Iterator[InvariantDecl]:
        for d in self.decls:
            if isinstance(d, InvariantDecl) and d.is_safety:
                yield d

    def definitions(self) -> Iterator[DefinitionDecl]:
        for d in self.decls:
            if isinstance(d, DefinitionDecl):
                yield d

    def transitions(self) -> Iterator[DefinitionDecl]:
        for d in self.definitions():
            if d.is_public_transition:
                yield d

    def axioms(self) -> Iterator[AxiomDecl]:
        for d in self.decls:
            if isinstance(d, AxiomDecl):
                yield d

    def theorems(self) -> Iterator[TheoremDecl]:
        for d in self.decls:
            if isinstance(d, TheoremDecl):
                yield d

    def constants(self) -> Iterator[ConstantDecl]:
        for d in self.decls:
            if isinstance(d, ConstantDecl):
                yield d

    def functions(self) -> Iterator[FunctionDecl]:
        for d in self.decls:
            if isinstance(d, FunctionDecl):
                yield d

    def relations_constants_and_functions(self) -> Iterator[StateDecl]:
        for d in self.decls:
            if isinstance(d, RelationDecl) or \
               isinstance(d, ConstantDecl) or \
               isinstance(d, FunctionDecl):
                yield d

    def derived_relations(self) -> Iterator[RelationDecl]:
        for d in self.decls:
            if isinstance(d, RelationDecl) and d.derived_axiom:
                yield d

    def decls_containing_exprs(self)\
        -> Iterator[Union[InitDecl, DefinitionDecl, InvariantDecl, AxiomDecl, TheoremDecl]]:
        for d in self.decls:
            if isinstance(d, InitDecl) or \
               isinstance(d, DefinitionDecl) or \
               isinstance(d, InvariantDecl) or \
               isinstance(d, AxiomDecl) or \
               isinstance(d, TheoremDecl):
                yield d

    def decls_quantifier_alternation_graph(self, additional: List[Expr]) -> DiGraph:
        res = quantifier_alternation_graph(self, [axiom.expr for axiom in self.axioms()] +
                                                 [cast(Expr, rel.derived_axiom) for rel in self.derived_relations()] +
                                                 additional)
        for f in self.functions():
            for asort in f.arity:
                esort = f.sort
                res.add_edge(self.scope.get_sort_checked(str(asort)).name,
                             self.scope.get_sort_checked(str(esort)).name)

        return res

    def automata(self) -> Iterator[AutomatonDecl]:
        for d in self.decls:
            if isinstance(d, AutomatonDecl):
                yield d

    def the_automaton(self) -> Optional[AutomatonDecl]:
        for d in self.automata():
            return d
        return None

    def traces(self) -> Iterator[TraceDecl]:
        for d in self.decls:
            if isinstance(d, TraceDecl):
                yield d

    def resolve_vocab(self) -> None:
        self.scope = scope = Scope[InferenceSort]()

        for s in self.sorts():
            s.resolve(scope)

        for rcf in self.relations_constants_and_functions():
            rcf.resolve(scope)

        for d in self.definitions():
            scope.add_definition(d)

    def resolve(self) -> None:
        self.resolve_vocab()

        for d in self.decls_containing_exprs():
            d.resolve(self.scope)

        for tr in self.traces():
            tr.resolve(self.scope)

        automata = list(self.automata())
        if len(automata) > 1:
            utils.print_error(automata[1].span, 'at most one automaton may be declared (first was declared at %s)' % (
                utils.loc_to_string(automata[0].span)
            ))

        if len(automata) > 0:
            a = automata[0]
            a.resolve(self.scope)

        assert len(self.scope.stack) == 0

    def __repr__(self) -> str:
        return 'Program(decls=%s)' % (self.decls,)

    def __str__(self) -> str:
        return '\n'.join(str(d) for d in self.decls)


def sort_from_z3sort(prog: Program, z3sort: z3.SortRef) -> SortDecl:
    return prog.scope.get_sort_checked(str(z3sort))

def qa_edges_expr(prog: Program, expr: Expr) -> Iterator[Tuple[str, str]]:
    lator = Z3Translator(cast(Scope[z3.ExprRef], prog.scope))
    z3expr = lator.translate_expr(expr)
    for (ssortz3, tsortz3) in z3_utils.z3_quantifier_alternations(z3expr):
        yield (sort_from_z3sort(prog, ssortz3).name,
               sort_from_z3sort(prog, tsortz3).name) # TODO: consider overriding equals instead of using the names


def quantifier_alternation_graph(prog: Program, exprs: List[Expr]) -> DiGraph:
    qa_graph = DiGraph()

    for expr in exprs:
        qa_graph.add_edges_from(qa_edges_expr(prog, expr))

    return qa_graph


the_program: Program = cast(Program, None)

@contextmanager
def prog_context(prog: Program) -> Iterator[None]:
    global the_program
    backup_prog = the_program
    the_program = prog
    yield None
    the_program = backup_prog
