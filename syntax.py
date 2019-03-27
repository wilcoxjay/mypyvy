from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
import itertools
import logging
import ply.lex
import sys
from typing import List, Union, Tuple, Optional, Dict, Iterator, \
    Callable, Any, NoReturn, Set, TypeVar, Generic, Iterable, Mapping, Sequence
from typing_extensions import Protocol
import utils
import z3

logger = logging.getLogger(__file__)
logger.setLevel(logging.DEBUG)


Token = ply.lex.LexToken

B = TypeVar('B')

class Sort(object):
    def __repr__(self) -> str:
        raise Exception('Unexpected sort %s does not implement __repr__ method' % type(self))

    def __str__(self) -> str:
        raise Exception('Unexpected sort %s does not implement __str__ method' % repr(self))

    def resolve(self, scope: Scope[B]) -> None:
        raise Exception('Unexpected sort %s does not implement resolve method' % repr(self))

    def to_z3(self) -> z3.SortRef:
        raise Exception('Unexpected sort %s does not implement to_z3 method' % repr(self))

    def _denote(self) -> object:
        raise Exception('Unexpected sort %s does not implement _denote method' % repr(self))

    def __hash__(self) -> int:
        return hash(self._denote())

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Sort):
            return False
        return self._denote() == other._denote()

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
    def __init__(self, scope: Scope[z3.ExprRef], key: Optional[str]=None, key_old: Optional[str]=None) -> None:
        self.scope = scope
        self.key = key
        self.key_old = key_old

    def bind(self, binder: Binder) -> List[z3.ExprRef]:
        bs = []
        for sv in binder.vs:
            n = sv.name
            assert sv.sort is not None and not isinstance(sv.sort, SortInferencePlaceholder)
            bs.append(z3.Const(n, sv.sort.to_z3()))
        return bs

    def translate_expr(self, expr: Expr, old: bool=False) -> z3.ExprRef:
        if isinstance(expr, Bool):
            return z3.BoolVal(expr.val)
        elif isinstance(expr, UnaryExpr):
            if expr.op == 'OLD':
                assert not old and self.key_old is not None
                return self.translate_expr(expr.arg, old=True)
            else:
                unop = z3_UNOPS[expr.op]
                assert unop is not None
                return unop(self.translate_expr(expr.arg, old))
        elif isinstance(expr, BinaryExpr):
            binop = z3_BINOPS[expr.op]
            return binop(self.translate_expr(expr.arg1, old), self.translate_expr(expr.arg2, old))
        elif isinstance(expr, NaryExpr):
            nop = z3_NOPS[expr.op]
            return nop([self.translate_expr(arg, old) for arg in expr.args])
        elif isinstance(expr, AppExpr):
            if not old:
                k = self.key
            else:
                assert self.key_old is not None
                k = self.key_old
            d = self.scope.get(expr.callee)
            assert d is not None
            if isinstance(d, DefinitionDecl):
                assert not (old and d.twostate)  # XXX check in resolver
                translated_args = [self.translate_expr(arg, old) for arg in expr.args]  # translate args in the scope of caller
                with self.scope.fresh_stack():
                    with self.scope.in_scope(d.binder, translated_args):
                        return self.translate_expr(d.expr, old)  # translate body of def in fresh scope
            else:
                assert isinstance(d, RelationDecl) or isinstance(d, FunctionDecl)
                R = d.to_z3(k)
                assert isinstance(R, z3.FuncDeclRef)
                app_translated_args = [self.translate_expr(arg, old) for arg in expr.args]
                translated_app = R(*app_translated_args)
                return translated_app
        elif isinstance(expr, QuantifierExpr):
            bs = self.bind(expr.binder)
            with self.scope.in_scope(expr.binder, bs):
                e = self.translate_expr(expr.body, old)
            q = z3.ForAll if expr.quant == 'FORALL' else z3.Exists
            return q(bs, e)
        elif isinstance(expr, Id):
            d = self.scope.get(expr.name)
            assert d is not None
            if isinstance(d, RelationDecl) or \
               isinstance(d, ConstantDecl) or \
               isinstance(d, FunctionDecl):
                if not old:
                    k = self.key
                else:
                    assert not d.mutable or self.key_old is not None
                    k = self.key_old
                x = d.to_z3(k)
                assert isinstance(x, z3.ExprRef)
                return x
            elif isinstance(d, DefinitionDecl):
                assert not (old and d.twostate)  # XXX check in resolver
                with self.scope.fresh_stack():
                    return self.translate_expr(d.expr, old)
            else:
                e, = d
                return e
        elif isinstance(expr, IfThenElse):
            return z3.If(self.translate_expr(expr.branch, old),
                         self.translate_expr(expr.then, old),
                         self.translate_expr(expr.els, old))
        elif isinstance(expr, Let):
            val = self.translate_expr(expr.val, old)
            with self.scope.in_scope(expr.binder, [val]):
                return self.translate_expr(expr.body, old)
        else:
            assert False


    def frame(self, mods: Iterable[ModifiesClause]) -> List[z3.ExprRef]:
        frame = []
        R: Iterator[StateDecl] = iter(self.scope.relations.values())
        C: Iterator[StateDecl] = iter(self.scope.constants.values())
        F: Iterator[StateDecl] = iter(self.scope.functions.values())
        for d in itertools.chain(R, C, F):
            if not d.mutable or (isinstance(d, RelationDecl) and d.is_derived()) or any(mc.name == d.name for mc in mods):
                continue

            if isinstance(d, ConstantDecl) or len(d.arity) == 0:
                lhs = d.to_z3(self.key)
                rhs = d.to_z3(self.key_old)
                assert isinstance(lhs, z3.ExprRef) and isinstance(rhs, z3.ExprRef)
                e = lhs == rhs
            else:
                cs: List[z3.ExprRef] = []
                i = 0
                for s in d.arity:
                    cs.append(z3.Const('x' + str(i), s.to_z3()))
                    i += 1

                lhs = d.to_z3(self.key)
                rhs = d.to_z3(self.key_old)
                assert isinstance(lhs, z3.FuncDeclRef) and isinstance(rhs, z3.FuncDeclRef)

                e = z3.Forall(cs, lhs(*cs) == rhs(*cs))

            frame.append(e)

        return frame

    def translate_transition_body(self, t: DefinitionDecl, precond: Optional[Expr]=None) -> z3.ExprRef:
        return z3.And(self.translate_expr(t.expr),
                      *self.frame(t.mods),
                      self.translate_expr(precond, old=True) if (precond is not None) else z3.BoolVal(True))

    def translate_transition(self, t: DefinitionDecl, precond: Optional[Expr]=None) -> z3.ExprRef:
        bs = self.bind(t.binder)
        with self.scope.in_scope(t.binder, bs):
            body = self.translate_transition_body(t, precond)
            if len(bs) > 0:
                return z3.Exists(bs, body)
            else:
                return body

    def translate_precond_of_transition(self, precond: Optional[Expr], t: DefinitionDecl) -> z3.ExprRef:
        bs = self.bind(t.binder)
        with self.scope.in_scope(t.binder, bs):
            body = self.translate_expr(precond, old=True) if (precond is not None) else z3.BoolVal(True)

            if len(bs) > 0:
                return z3.Exists(bs, body)
            else:
                return body


def symbols_used(scope: Scope, expr: Expr, old: bool=False) -> Set[Tuple[bool, Optional[Token], str]]:
    if isinstance(expr, Bool):
        return set()
    elif isinstance(expr, UnaryExpr):
        if expr.op == 'OLD':
            assert not old
            return symbols_used(scope, expr.arg, old=True)
        else:
            return symbols_used(scope, expr.arg, old)
    elif isinstance(expr, BinaryExpr):
        return symbols_used(scope, expr.arg1, old) | symbols_used(scope, expr.arg2,old)
    elif isinstance(expr, NaryExpr):
        ans: Set[Tuple[bool, Optional[Token], str]] = set()
        for arg in expr.args:
            ans |= symbols_used(scope, arg, old)
        return ans
    elif isinstance(expr, AppExpr):
        args: Set[Tuple[bool, Optional[Token], str]] = set()
        for arg in expr.args:
            args |= symbols_used(scope, arg, old)

        d = scope.get(expr.callee)
        assert d is not None and not isinstance(d, tuple)
        if isinstance(d, DefinitionDecl):
            assert not (old and d.twostate)
            with scope.fresh_stack():
                with scope.in_scope(d.binder, [None for i in range(len(d.binder.vs))]):
                    return args | symbols_used(scope, d.expr, old)
        elif d.mutable:
            return args | {(old, expr.tok, expr.callee)}
        else:
            return args
    elif isinstance(expr, QuantifierExpr):
        with scope.in_scope(expr.binder, [None for i in range(len(expr.binder.vs))]):
            return symbols_used(scope, expr.body, old)
    elif isinstance(expr, Id):
        d = scope.get(expr.name)
        assert d is not None, expr.name
        if (isinstance(d, RelationDecl) or \
            isinstance(d, ConstantDecl) or \
            isinstance(d, FunctionDecl)) and \
            d.mutable:
            return {(old, expr.tok, expr.name)}
        else:
            return set()
    elif isinstance(expr, IfThenElse):
        return symbols_used(scope, expr.branch, old) | \
               symbols_used(scope, expr.then, old) | \
               symbols_used(scope, expr.els, old)
    elif isinstance(expr, Let):
        s1 = symbols_used(scope, expr.val, old)
        with scope.in_scope(expr.binder, [None for i in range(len(expr.binder.vs))]):
            return s1 | symbols_used(scope, expr.body, old)
    else:
        assert False


def subst_vars_simple(expr: Expr, subst: Mapping[Id, Expr]) -> Expr:
    if isinstance(expr, Bool):
        return expr
    elif isinstance(expr, UnaryExpr):
        return UnaryExpr(tok=None, op=expr.op, arg=subst_vars_simple(expr.arg, subst))
    elif isinstance(expr, BinaryExpr):
        return BinaryExpr(tok=None, op=expr.op, arg1=subst_vars_simple(expr.arg1, subst),
                                                arg2=subst_vars_simple(expr.arg2, subst))
    elif isinstance(expr, AppExpr):
        return AppExpr(tok=None, callee=expr.callee, args=[subst_vars_simple(a, subst) for a in expr.args])
    elif isinstance(expr, Id):
        return subst.get(expr, expr)
    else:
        print(expr)
        assert False


class Expr(object):
    def __repr__(self) -> str:
        raise Exception('Unexpected expr %s does not implement __repr__ method' % type(self))

    def __str__(self) -> str:
        buf: List[str] = []
        self.pretty(buf, PREC_TOP, 'NONE')
        return ''.join(buf)

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        raise Exception('Unexpected expression %s does not implement resolve method' %
                        repr(self))

    def _denote(self) -> object:
        raise Exception('Unexpected expr %s does not implement _denote method' % repr(self))

    def __hash__(self) -> int:
        return hash(self._denote())

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Expr):
            return False
        return self._denote() == other._denote()

    def __ne__(self, other: object) -> bool:
        return not (self == other)

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
    def __init__(self, tok: Optional[Token], val: bool) -> None:
        self.tok = tok
        self.val = val

    def __repr__(self) -> str:
        return str(self.val)

    def _denote(self) -> object:
        return self.val

    def prec(self) -> int:
        return PREC_BOT

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        buf.append('true' if self.val else 'false')

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        check_constraint(self.tok, sort, BoolSort)
        return BoolSort

    def free_ids(self) -> List[str]:
        return []

TrueExpr  = Bool(None, True)
FalseExpr = Bool(None, False)

UNOPS = {
    'NOT',
    'OLD'
}
z3_UNOPS: Dict[str, Optional[Callable[[z3.ExprRef], z3.ExprRef]]] = {
    'NOT': z3.Not,
    'OLD': None
}

def check_constraint(tok: Optional[Token], expected: InferenceSort, actual: InferenceSort) -> InferenceSort:
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
                utils.print_error(tok, 'expected sort %s but got %s' % (expected, actual))
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
    def __init__(self, tok: Optional[Token], op: str, arg: Expr) -> None:
        assert op in UNOPS
        self.tok = tok
        self.op = op
        self.arg = arg

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        if self.op == 'OLD':
            if not scope.in_two_state_context:
                utils.print_error(self.tok, 'old can only be used in a two-state context')
            if scope.in_old_context:
                utils.print_error(self.tok, 'old() expression cannot be nested inside another old!')
            with scope.old_context():
                return self.arg.resolve(scope, sort)
        else:
            assert self.op == 'NOT'
            check_constraint(self.tok, sort, BoolSort)
            self.arg.resolve(scope, BoolSort)
            return BoolSort

    def _denote(self) -> object:
        return (UnaryExpr, self.op, self.arg)

    def __repr__(self) -> str:
        return 'UnaryExpr(tok=None, op=%s, arg=%s)' % (repr(self.op), repr(self.arg))

    def prec(self) -> int:
        if self.op == 'NOT':
            return PREC_NOT
        elif self.op == 'OLD':
            return PREC_BOT
        else:
            assert False

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        if self.op == 'NOT':
            buf.append('!')
            self.arg.pretty(buf, PREC_NOT, 'NONE')
        elif self.op == 'OLD':
            buf.append('old(')
            self.arg.pretty(buf, PREC_TOP, 'NONE')
            buf.append(')')
        else:
            assert False

    def free_ids(self) -> List[str]:
        return self.arg.free_ids()

def Not(e: Expr) -> Expr:
    return UnaryExpr(None, 'NOT', e)

def Old(e: Expr) -> Expr:
    return UnaryExpr(None, 'OLD', e)

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
    def __init__(self, tok: Optional[Token], op: str, arg1: Expr, arg2: Expr) -> None:
        assert op in BINOPS
        self.tok = tok
        self.op = op
        self.arg1 = arg1
        self.arg2 = arg2

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        check_constraint(self.tok, sort, BoolSort)

        if self.op in ['AND', 'OR', 'IMPLIES', 'IFF']:
            self.arg1.resolve(scope, BoolSort)
            self.arg2.resolve(scope, BoolSort)
        else:
            assert self.op in ['EQUAL', 'NOTEQ']
            s = self.arg1.resolve(scope, None)
            self.arg2.resolve(scope, s)

        return BoolSort


    def _denote(self) -> object:
        return (BinaryExpr, self.op, self.arg1, self.arg2)

    def __repr__(self) -> str:
        return 'BinaryExpr(tok=None, op=%s, arg1=%s, arg2=%s)' % (
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
}

z3_NOPS: Any = {
    'AND' : z3.And,
    'OR' : z3.Or
}

class NaryExpr(Expr):
    def __init__(self, tok: Optional[Token], op: str, args: List[Expr]) -> None:
        assert op in NOPS
        assert len(args) >= 2, (args, tok)

        self.tok = tok
        self.op = op
        self.args = args

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        check_constraint(self.tok, sort, BoolSort)

        for arg in self.args:
            arg.resolve(scope, BoolSort)

        return BoolSort

    def _denote(self) -> object:
        return (NaryExpr, self.op, tuple(self.args))

    def __repr__(self) -> str:
        return 'NaryExpr(tok=None, op=%s, args=%s)' % (repr(self.op), self.args)

    def prec(self) -> int:
        if self.op == 'AND':
            return PREC_AND
        elif self.op == 'OR':
            return PREC_OR
        else:
            assert False

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        assert len(self.args) >= 2

        p = self.prec()

        if self.op == 'AND':
            s = '&'
        elif self.op == 'OR':
            s = '|'
        else:
            assert False

        self.args[0].pretty(buf, p, 'LEFT')

        for arg in self.args[1:-1]:
            buf.append(' %s ' % s)
            arg.pretty(buf, p, 'LEFT')

        buf.append(' %s ' % s)

        self.args[-1].pretty(buf, p, 'RIGHT')

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
    return QuantifierExpr(None, 'FORALL', vs, body)

def Exists(vs: List[SortedVar], body: Expr) -> Expr:
    return QuantifierExpr(None, 'EXISTS', vs, body)

def And(*args: Expr) -> Expr:
    if len(args) == 0:
        return Bool(None, True)
    elif len(args) == 1:
        return args[0]
    else:
        return NaryExpr(None, 'AND', list(args))

def Or(*args: Expr) -> Expr:
    if len(args) == 0:
        return Bool(None, False)
    elif len(args) == 1:
        return args[0]
    else:
        return NaryExpr(None, 'OR', list(args))

def Eq(arg1: Expr, arg2: Expr) -> Expr:
    return BinaryExpr(None, 'EQUAL', arg1, arg2)

def Neq(arg1: Expr, arg2: Expr) -> Expr:
    return BinaryExpr(None, 'NOTEQ', arg1, arg2)

def Iff(arg1: Expr, arg2: Expr) -> Expr:
    return BinaryExpr(None, 'IFF', arg1, arg2)

def Apply(callee: str, args: List[Expr]) -> Expr:
    return AppExpr(None, callee, args)

class AppExpr(Expr):
    def __init__(self, tok: Optional[Token], callee: str, args: List[Expr]) -> None:
        if not (len(args) > 0):
            utils.print_error(tok, "must be applied to at least one argument")
        self.tok = tok
        self.callee = callee
        self.args = args

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        d = scope.get(self.callee)
        if d is None:
            utils.print_error(self.tok, 'Unresolved relation or function name %s' % self.callee)
            return sort  # bogus

        if not (isinstance(d, RelationDecl) or isinstance(d, FunctionDecl) or isinstance(d, DefinitionDecl)):
            utils.print_error(self.tok, 'Only relations, functions, or definitions can be applied, not %s' % self.callee)
            return sort  # bogus

        if len(d.arity) == 0 or len(self.args) != len(d.arity):
            utils.print_error(self.tok, 'Callee applied to wrong number of arguments')
        for (arg, s) in zip(self.args, d.arity):
            arg.resolve(scope, s)

        if isinstance(d, RelationDecl):
            check_constraint(self.tok, sort, BoolSort)
            return BoolSort
        else:
            sort = check_constraint(self.tok, sort, d.sort)
            return sort

    def _denote(self) -> object:
        return (AppExpr, self.callee, tuple(self.args))

    def __repr__(self) -> str:
        return 'AppExpr(tok=None, rel=%s, args=%s)' % (repr(self.callee), self.args)

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

class SortedVar(object):
    def __init__(self, tok: Optional[Token], name: str, sort: Optional[Sort]) -> None:
        self.tok = tok
        self.name = name
        self.sort: InferenceSort = sort

    def resolve(self, scope: Scope[InferenceSort]) -> None:
        if self.sort is None:
            utils.print_error(self.tok, 'type annotation required for variable %s' % (self.name,))
            return

        assert not isinstance(self.sort, SortInferencePlaceholder)

        self.sort.resolve(scope)

    def __repr__(self) -> str:
        return 'SortedVar(tok=None, name=%s, sort=%s)' % (repr(self.name), repr(self.sort))

    def __str__(self) -> str:
        if self.sort is None:
            return self.name
        else:
            return '%s:%s' % (self.name, self.sort)


class Binder(object):
    def __init__(self, vs: List[SortedVar]) -> None:
        self.vs = vs

    def __repr__(self) -> str:
        return 'Binder(%s)' % self.vs

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
                utils.print_error(sv.tok, 'Could not infer sort for variable %s' % (sv.name,))


class QuantifierExpr(Expr):
    def __init__(self, tok: Optional[Token], quant: str, vs: List[SortedVar], body: Expr) -> None:
        assert quant in ['FORALL', 'EXISTS']
        assert len(vs) > 0
        self.tok = tok
        self.quant = quant
        self.binder = Binder(vs)
        self.body = body

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        check_constraint(self.tok, sort, BoolSort)

        self.binder.pre_resolve(scope)

        with scope.in_scope(self.binder, [v.sort for v in self.binder.vs]):
            self.body.resolve(scope, BoolSort)

        self.binder.post_resolve()

        return BoolSort

    def __repr__(self) -> str:
        return 'QuantifierExpr(tok=None, quant=%s, vs=%s, body=%s)' % (repr(self.quant), self.binder.vs, repr(self.body))

    def _denote(self) -> object:
        return (QuantifierExpr, self.quant, self.body)

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

class Id(Expr):
    '''Unresolved symbol (might represent a constant or a nullary relation or a variable)'''
    def __init__(self, tok: Optional[Token], name: str) -> None:
        self.tok = tok
        self.name = name

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        d = scope.get(self.name)

        if d is None:
            utils.print_error(self.tok, 'Unresolved variable %s' % (self.name,))
            return sort  # bogus

        if isinstance(d, FunctionDecl):
            utils.print_error(self.tok, 'Function %s must be applied to arguments' % (self.name,))
            return sort  # bogus

        if isinstance(d, RelationDecl):
            if len(d.arity) > 0:
                utils.print_error(self.tok, 'Relation %s must be applied to arguments' % (self.name,))
                return sort  # bogus
            check_constraint(self.tok, sort, BoolSort)
            return BoolSort
        elif isinstance(d, ConstantDecl):
            sort = check_constraint(self.tok, sort, d.sort)
            return sort
        elif isinstance(d, DefinitionDecl):
            if len(d.arity) > 0:
                utils.print_error(self.tok, 'Definition %s must be applied to arguments' % (self.name,))
                return sort  # bogus
            check_constraint(self.tok, sort, d.sort)
            return BoolSort
        else:
            vsort, = d
            vsort = check_constraint(self.tok, sort, vsort)
            return vsort

    def _denote(self) -> object:
        return (Id, self.name)

    def __repr__(self) -> str:
        return 'Id(tok=None, name=%s)' % (repr(self.name),)

    def prec(self) -> int:
        return PREC_BOT

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        buf.append(self.name)

    def free_ids(self) -> List[str]:
        return [self.name]

class IfThenElse(Expr):
    def __init__(self, tok: Optional[Token], branch: Expr, then: Expr, els: Expr) -> None:
        self.tok = tok
        self.branch = branch
        self.then = then
        self.els = els

    def __repr__(self) -> str:
        return 'IfThenElse(%s, %s, %s)' % (self.branch, self.then, self.els)

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        self.branch.resolve(scope, BoolSort)
        sort = self.then.resolve(scope, sort)
        return self.els.resolve(scope, sort)

    def _denote(self) -> object:
        return (IfThenElse, self.branch, self.then, self.els)

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
    def __init__(self, tok: Optional[Token], var: SortedVar, val: Expr, body: Expr) -> None:
        self.tok = tok
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

    def _denote(self) -> object:
        return (Let, self.binder, self.val, self.body)

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
    def __init__(self, tok: Optional[Token], name: str) -> None:
        self.tok = tok
        self.name = name
        self.decl: Optional[SortDecl] = None

    def resolve(self, scope: Scope) -> None:
        self.decl = scope.get_sort(self.name)
        if self.decl is None:
            utils.print_error(self.tok, 'Unresolved sort name %s' % (self.name,))

    def __repr__(self) -> str:
        return 'UninterpretedSort(tok=None, name=%s)' % (repr(self.name),)

    def __str__(self) -> str:
        return self.name

    def to_z3(self) -> z3.SortRef:
        assert self.decl is not None

        return self.decl.to_z3()

    def _denote(self) -> object:
        return (UninterpretedSort, self.name)

class _BoolSort(Sort):
    def __repr__(self) -> str:
        return 'bool'

    def __str__(self) -> str:
        return 'bool'

    def resolve(self, scope: Scope) -> None:
        pass

    def to_z3(self) -> z3.SortRef:
        return z3.BoolSort()

    def _denote(self) -> object:
        return _BoolSort

BoolSort = _BoolSort()

class AssumeStatement(object):
    def __init__(self, tok: Optional[Token], expr: Expr) -> None:
        self.tok = tok
        self.expr = expr

    def __repr__(self) -> str:
        return 'AssumeStatement(tok=None, expr=%s)' % self.expr

class AssignmentStatement(object):
    def __init__(self, tok: Optional[Token], assignee: str, args: List[Expr], rhs: Expr) -> None:
        self.tok = tok
        self.assignee = assignee
        self.args = args
        self.rhs = rhs

    def __repr__(self) -> str:
        return 'AssignmentStatement(tok=None, assignee=%s, args=%s, rhs=%s)' % (self.assignee, self.args, self.rhs)

Statement = Union[AssumeStatement, AssignmentStatement]

class BlockStatement(object):
    def __init__(self, tok: Optional[Token], stmts: List[Statement]) -> None:
        self.tok = tok
        self.stmts = stmts

    def __repr__(self) -> str:
        return 'BlockStatement(tok=None, stmts=%s)' % self.stmts

def translate_block(block: BlockStatement) -> Tuple[List[ModifiesClause], Expr]:
    mods_str_list: List[str] = []
    conjuncts = []
    for stmt in block.stmts:
        if isinstance(stmt, AssumeStatement):
            conjuncts.append(Old(stmt.expr))
        elif isinstance(stmt, AssignmentStatement):
            assert stmt.assignee not in mods_str_list
            mods_str_list.append(stmt.assignee)
            if len(stmt.args) == 0:
                conjuncts.append(Eq(Id(None, stmt.assignee), stmt.rhs))
            else:
                assert isinstance(stmt.rhs, Bool)
                if stmt.rhs.val:
                    f = lambda x, y: Or(x, y)
                else:
                    f = lambda x, y: And(x, Not(y))
                vs = ['X%s' % i for i, _ in enumerate(stmt.args)]
                c = And(*(Eq(Id(None, X), arg) for X, arg in zip(vs, stmt.args)))

                conjuncts.append(Forall([SortedVar(None, v, None) for v in vs],
                                        Iff(Apply(stmt.assignee, [Id(None, v) for v in vs]),
                                            f(Old(Apply(stmt.assignee, [Id(None, v) for v in vs])), c))))
        else:
            reveal_type(stmt)
            assert False
    return ([ModifiesClause(None, name) for name in mods_str_list], And(*conjuncts))

class Decl(object):
    def __repr__(self) -> str:
        raise Exception('Unexpected decl %s does not implement __repr__ method' % type(self))

    def __str__(self) -> str:
        raise Exception('Unexpected decl %s does not implement __str__ method' % type(self))


class SortDecl(Decl):
    def __init__(self, tok: Optional[Token], name: str) -> None:
        self.tok = tok
        self.name = name
        self.z3: Optional[z3.SortRef] = None

    def resolve(self, scope: Scope) -> None:
        scope.add_sort(self)

    def __repr__(self) -> str:
        return 'SortDecl(tok=None, name=%s)' % (repr(self.name), )

    def __str__(self) -> str:
        return 'sort %s' % self.name

    def to_z3(self) -> z3.SortRef:
        if self.z3 is None:
            self.z3 = z3.DeclareSort(self.name)

        return self.z3

class FunctionDecl(Decl):
    def __init__(self, tok: Optional[Token], name: str, arity: Arity, sort: Sort, mutable: bool) -> None:
        self.tok = tok
        self.name = name
        self.arity = arity
        self.sort = sort
        self.mutable = mutable
        self.mut_z3: Dict[str, z3.FuncDeclRef] = {}
        self.immut_z3: Optional[z3.FuncDeclRef] = None

        assert len(self.arity) > 0

    def resolve(self, scope: Scope) -> None:
        for sort in self.arity:
            sort.resolve(scope)

        self.sort.resolve(scope)

        scope.add_function(self)

    def __repr__(self) -> str:
        return 'FunctionDecl(tok=None, name=%s, arity=%s, sort=%s, mutable=%s)' % (
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
    def __init__(self, tok: Optional[Token], name: str, arity: Arity, mutable: bool, derived: Optional[Expr]=None) -> None:
        self.tok = tok
        self.name = name
        self.arity = arity
        self.mutable = mutable
        self.mut_z3: Dict[str, Union[z3.FuncDeclRef, z3.ExprRef]] = {}
        self.immut_z3: Optional[Union[z3.FuncDeclRef, z3.ExprRef]] = None
        self.derived_axiom = derived

    def resolve(self, scope: Scope) -> None:
        for sort in self.arity:
            sort.resolve(scope)

        scope.add_relation(self)

        if self.derived_axiom:
            self.derived_axiom = close_free_vars(self.tok, self.derived_axiom)
            self.derived_axiom.resolve(scope, BoolSort)

    def __repr__(self) -> str:
        return 'RelationDecl(tok=None, name=%s, arity=%s, mutable=%s, derived=%s)' % (repr(self.name), self.arity, self.mutable, self.derived_axiom)

    def __str__(self) -> str:
        return '%s relation %s(%s)%s' % ('mutable' if self.mutable else 'immutable',
                                       self.name,
                                       ', '.join([str(s) for s in self.arity]),
                                         '' if not self.derived_axiom else (': %s' % str(self.derived_axiom)))

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
    def __init__(self, tok: Optional[Token], name: str, sort: Sort, mutable: bool) -> None:
        self.tok = tok
        self.name = name
        self.sort = sort
        self.mutable = mutable
        self.mut_z3: Dict[str, z3.ExprRef] = {}
        self.immut_z3: Optional[z3.ExprRef] = None


    def __repr__(self) -> str:
        return 'ConstantDecl(tok=None, name=%s, sort=%s, mutable=%s)' % (repr(self.name), self.sort, self.mutable)

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

def close_free_vars(tok: Optional[Token], expr: Expr, in_scope: List[str]=[]) -> Expr:
    vs = [s for s in expr.free_ids() if s not in in_scope and s.isupper()]
    if vs == []:
        return expr
    else:
        # logging.debug('closing expression')
        # logging.debug(str(expr))
        # logging.debug('with free vars %s' % vs)
        return QuantifierExpr(None, 'FORALL', [SortedVar(tok, v, None) for v in vs], expr)

class InitDecl(Decl):
    def __init__(self, tok: Optional[Token], name: Optional[str], expr: Expr) -> None:
        self.tok = tok
        self.name = name
        self.expr = expr

    def resolve(self, scope: Scope) -> None:
        self.expr = close_free_vars(self.tok, self.expr)
        self.expr.resolve(scope, BoolSort)

        if symbols_used(scope, self.expr) == set():
            utils.print_error(self.tok, 'this initial condition mentions no mutable symbols. it should be declared `axiom` instead.')

    def __repr__(self) -> str:
        return 'InitDecl(tok=None, name=%s, expr=%s)' % (
            repr(self.name) if self.name is not None else 'None',
            repr(self.expr))

    def __str__(self) -> str:
        return 'init %s%s' % (('[%s] ' % self.name) if self.name is not None else '',
                              self.expr)

class ModifiesClause(object):
    def __init__(self, tok: Optional[Token], name: str) -> None:
        self.tok = tok
        self.name = name

    def resolve(self, scope: Scope[InferenceSort]) -> None:
        d = scope.get(self.name)
        assert d is None or isinstance(d, RelationDecl) or \
            isinstance(d, ConstantDecl) or isinstance(d, FunctionDecl)
        if d is None:
            utils.print_error(self.tok, 'Unresolved constant, relation, or function %s' % (self.name,))

    def __repr__(self) -> str:
        return 'ModifiesClause(tok=None, name=%s)' % (repr(self.name),)

    def __str__(self) -> str:
        return self.name

class DefinitionDecl(Decl):
    def __init__(self, tok: Optional[Token], public: bool, twostate: bool, name: str,
                 params: List[SortedVar],
                 body: Union[BlockStatement, Tuple[List[ModifiesClause], Expr]]) -> None:
        def implies(a: bool, b: bool) -> bool:
            return not a or b
        # these asserts are enforced by the parser
        assert implies(public, twostate)
        assert isinstance(body, BlockStatement) or len(body[0]) == 0 or twostate

        self.tok = tok
        self.public = public
        self.twostate = twostate
        self.name = name
        self.binder = Binder(params)
        self.arity = [sv.sort for sv in params]
        self.sort = BoolSort
        self.body = body
        if isinstance(self.body, BlockStatement):
            self.mods, self.expr = translate_block(self.body)
        else:
            self.mods, self.expr = self.body

    def resolve(self, scope: Scope) -> None:
        assert len(scope.stack) == 0

        old_error_count = 0

        scope.add_definition(self)

        self.binder.pre_resolve(scope)

        for mod in self.mods:
            mod.resolve(scope)

        self.expr = close_free_vars(self.tok, self.expr, in_scope=[v.name for v in self.binder.vs])

        with scope.in_scope(self.binder, [v.sort for v in self.binder.vs]):
            with scope.two_state(self.twostate):
                self.expr.resolve(scope, BoolSort)

        self.binder.post_resolve()

        if utils.error_count > old_error_count:
            return

        if self.twostate:
            with scope.in_scope(self.binder, [v.sort for v in self.binder.vs]):
                syms = symbols_used(scope, self.expr)
                for is_old, tok, sym in syms:
                    if not is_old:
                        for mod in self.mods:
                            if mod.name == sym:
                                break
                        else:
                            utils.print_error(tok, 'symbol %s is referred to in the new state, but is not mentioned in the modifies clause' % sym)

                for mod in self.mods:
                    for is_old, tok, sym in syms:
                        if mod.name == sym and not is_old:
                            break
                    else:
                        utils.print_error(mod.tok, 'symbol %s is mentioned by the modifies clause, but is not referred to in the new state, so it will be havoced. supress this error by using %s in a no-op.' % (mod.name, mod.name))

    def __repr__(self) -> str:
        return 'TransitionDecl(tok=None, name=%s, params=%s, mods=%s, expr=%s)' % (
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
    def __init__(self, tok: Optional[Token], name: Optional[str], expr: Expr, is_safety: bool, is_sketch: bool) -> None:
        self.tok = tok
        self.name = name
        self.expr = expr
        self.is_safety = is_safety
        self.is_sketch = is_sketch

    def resolve(self, scope: Scope) -> None:
        self.expr = close_free_vars(self.tok, self.expr)
        self.expr.resolve(scope, BoolSort)

        if symbols_used(scope, self.expr) == set():
            utils.print_error(self.tok, 'this invariant mentions no mutable symbols. it can be deleted.')

    def __repr__(self) -> str:
        return 'InvariantDecl(tok=None, name=%s, expr=%s, is_safety=%s, is_sketch=%s)' % (
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
    def __init__(self, tok: Optional[Token], name: Optional[str], expr: Expr) -> None:
        self.tok = tok
        self.name = name
        self.expr = expr

    def resolve(self, scope: Scope) -> None:
        self.expr = close_free_vars(self.tok, self.expr)
        self.expr.resolve(scope, BoolSort)

    def __repr__(self) -> str:
        return 'AxiomDecl(tok=None, name=%s, expr=%s)' % (
            repr(self.name) if self.name is not None else 'None',
            repr(self.expr))

    def __str__(self) -> str:
        return 'axiom %s%s' % (('[%s] ' % self.name) if self.name is not None else '',
                               self.expr)

class TheoremDecl(Decl):
    def __init__(self, tok: Optional[Token], name: Optional[str], expr: Expr, twostate: bool) -> None:
        self.tok = tok
        self.name = name
        self.expr = expr
        self.twostate = twostate

    def resolve(self, scope: Scope) -> None:
        self.expr = close_free_vars(self.tok, self.expr)
        self.expr.resolve(scope, BoolSort)

    def __repr__(self) -> str:
        return 'TheoremDecl(tok=None, name=%s, expr=%s, twostate=%s)' % (
            repr(self.name) if self.name is not None else 'None',
            repr(self.expr),
            self.twostate
        )

    def __str__(self) -> str:
        return '%stheorem %s%s' % (
            'twostate ' if self.twostate else '',
            ('[%s] ' % self.name) if self.name is not None else '',
            self.expr
        )

## decls inside an automaton block

class PhaseTransitionDecl(object):
    def __init__(self, tok: Optional[Token], transition: str, precond: Optional[Expr], target: Optional[str]) -> None:
        self.tok = tok
        self.transition = transition
        self.precond = precond
        self.target = target

    def __repr__(self) -> str:
        return 'PhaseTransitionDecl(tok=None, transition=%s, target=%s, precond=%s)' % (
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
            utils.print_error(self.tok, 'unknown transition %s' % (self.transition,))
            return

        if self.precond is not None:
            transition_constants = transition.binder.vs
            self.precond = close_free_vars(self.tok, self.precond, in_scope=[x.name for x in transition_constants])
            with scope.in_scope(transition.binder, [v.sort for v in transition_constants]):
                self.precond.resolve(scope, BoolSort)

        if self.target is not None and scope.get_phase(self.target) is None:
            utils.print_error(self.tok, 'unknown phase %s' % (self.target))

PhaseComponent = Union[PhaseTransitionDecl, InvariantDecl]

class GlobalPhaseDecl(object):
    def __init__(self, tok: Optional[Token], components: Sequence[PhaseComponent]) -> None:
        self.tok = tok
        self.components = components

    def __repr__(self) -> str:
        return 'GlobalPhaseDecl(tok=None, components=%s)' % (
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

class InitPhaseDecl(object):
    def __init__(self, tok: Optional[Token], phase: str) -> None:
        self.tok = tok
        self.phase = phase

    def __repr__(self) -> str:
        return 'InitPhaseDecl(tok=None, phase=%s)' % (
            self.phase,
        )

    def __str__(self) -> str:
        return 'init phase %s' % (
            self.phase,
        )

    def resolve(self, scope: Scope) -> None:
        if scope.get_phase(self.phase) is None:
            utils.print_error(self.tok, 'unknown phase %s' % (self.phase,))


class PhaseDecl(object):
    def __init__(self, tok: Optional[Token], name: str, components: Sequence[PhaseComponent]) -> None:
        self.tok = tok
        self.name = name
        self.components = components

    def __repr__(self) -> str:
        return 'PhaseDecl(tok=None, name=%s, components=%s)' % (
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
    def __init__(self, tok: Optional[Token], components: Sequence[AutomatonComponent]) -> None:
        self.tok = tok
        self.components = components

    def inits(self) -> Iterator[InitPhaseDecl]:
        for c in self.components:
            if isinstance(c, InitPhaseDecl):
                yield c

    def the_init(self) -> Optional[InitPhaseDecl]:
        i = list(self.inits())
        if len(i) == 0:
            utils.print_error(self.tok, 'automaton must declare an initial phase')
            return None
        elif len(i) > 1:
            utils.print_error(self.tok, 'automaton may only declare one initial phase')

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
        return 'AutomatonDecl(tok=None, components=%s)' % (
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

@dataclass
class AnyTransition(object):
    def __str__(self) -> str:
        return 'any transition'

    def resolve(self, scope: Scope) -> None:
        pass

@dataclass
class Star(object):
    def __str__(self) -> str:
        return '*'

@dataclass
class TransitionCall(object):
    tok: Optional[Token]
    target: str
    args: Optional[List[Union[Star, Expr]]]

    def __str__(self) -> str:
        return '%s%s' % (
            self.target,
            '' if self.args is None
            else '(%s)' % ', '.join(str(a) for a in self.args)
        )

    def resolve(self, scope: Scope) -> None:
        ition = scope.get_definition(self.target)
        if ition is None:
            utils.print_error(self.tok, 'could not find transition %s' % (self.target,))
            return

        if self.args is not None:
            if len(self.args) != len(ition.binder.vs):
                utils.print_error(self.tok, 'transition applied to the wrong number of arguments (expected %s, got %s)' % (len(ition.binder.vs), len(self.args)))
                return

            for a, sort in zip(self.args, (v.sort for v in ition.binder.vs)):
                if isinstance(a, Expr):
                    a.resolve(scope, sort)

@dataclass
class TransitionCalls(object):
    calls: List[TransitionCall]

    def __str__(self) -> str:
        return ' | '.join(str(c) for c in self.calls)

    def resolve(self, scope: Scope) -> None:
        for c in self.calls:
            c.resolve(scope)

TransitionExpr = Union[AnyTransition, TransitionCalls]

@dataclass
class TraceTransitionDecl(object):
    transition: TransitionExpr

    def __str__(self) -> str:
        return str(self.transition)

    def resolve(self, scope: Scope) -> None:
        self.transition.resolve(scope)


@dataclass
class AssertDecl(object):
    tok: Optional[Token]
    expr: Expr

    def __str__(self) -> str:
        return 'assert %s' % (str(self.expr),)

    def resolve(self, scope: Scope) -> None:
        self.expr = close_free_vars(self.tok, self.expr)
        self.expr.resolve(scope, BoolSort)


TraceComponent = Union[TraceTransitionDecl, AssertDecl] # , AxiomDecl, ConstantDecl]

@dataclass
class TraceDecl(Decl):
    components: List[TraceComponent]

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

class Scope(Generic[B]):
    def __init__(self) -> None:
        self.stack: List[List[Tuple[str, B]]] = []
        self.sorts: Dict[str, SortDecl] = {}
        self.relations: Dict[str, RelationDecl] = {}
        self.constants: Dict[str, ConstantDecl] = {}
        self.functions: Dict[str, FunctionDecl] = {}
        self.definitions: Dict[str, DefinitionDecl] = {}
        self.phases: Dict[str, PhaseDecl] = {}
        self.in_two_state_context = False
        self.in_old_context = False

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

    def _check_duplicate_name(self, tok: Optional[Token], name: str) -> None:
        if name in self.constants:
            utils.print_error(tok, 'Name %s is already declared as a constant' % (name,))

        if name in self.relations:
            utils.print_error(tok, 'Name %s is already declared as a relation' % (name,))

        if name in self.functions:
            utils.print_error(tok, 'Name %s is already declared as a function' % (name,))

        if name in self.definitions:
            utils.print_error(tok, 'Name %s is already declared as a definition' % (name,))


    def add_sort(self, decl: SortDecl) -> None:
        assert len(self.stack) == 0

        tok = decl.tok
        sort = decl.name

        if sort in self.sorts:
            utils.print_error(tok, 'Duplicate sort name %s' % (sort,))

        self.sorts[sort] = decl

    def get_sort(self, sort: str) -> Optional[SortDecl]:
        return self.sorts.get(sort)

    def add_constant(self, decl: ConstantDecl) -> None:
        assert len(self.stack) == 0

        self._check_duplicate_name(decl.tok, decl.name)
        self.constants[decl.name] = decl

    def add_relation(self, decl: RelationDecl) -> None:
        assert len(self.stack) == 0

        self._check_duplicate_name(decl.tok, decl.name)
        self.relations[decl.name] = decl

    def add_function(self, decl: FunctionDecl) -> None:
        assert len(self.stack) == 0

        self._check_duplicate_name(decl.tok, decl.name)
        self.functions[decl.name] = decl

    def add_phase(self, decl: PhaseDecl) -> None:
        assert len(self.stack) == 0

        if decl.name is not None:
            if decl.name in self.phases:
                utils.print_error(decl.tok, 'there is already a phase named %s' % decl.name)
            self.phases[decl.name] = decl

    def get_phase(self, phase: str) -> Optional[PhaseDecl]:
        return self.phases.get(phase)

    def add_definition(self, decl: DefinitionDecl) -> None:
        assert len(self.stack) == 0

        self._check_duplicate_name(decl.tok, decl.name)
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
    def old_context(self) -> Iterator[None]:
        old = self.in_old_context
        self.in_old_context = True
        yield None
        self.in_old_context = old

    @contextmanager
    def two_state(self, twostate: bool) -> Iterator[None]:
        if twostate:
            assert not self.in_two_state_context
            self.in_two_state_context = True
        yield None
        if twostate:
            self.in_two_state_context = False

    @contextmanager
    def in_scope(self, b: Binder, annots: List[B]) -> Iterator[None]:
        n = len(self.stack)
        assert len(b.vs) == len(annots)
        self.push(list(zip((v.name for v in b.vs), annots)))
        yield
        self.pop()
        assert n == len(self.stack)

StateDecl = Union[RelationDecl, ConstantDecl, FunctionDecl]

class Program(object):
    def __init__(self, decls: List[Decl]) -> None:
        self.decls = decls
        self.scope: Scope[InferenceSort]

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
            if d.public:
                yield d

    def axioms(self) -> Iterator[AxiomDecl]:
        for d in self.decls:
            if isinstance(d, AxiomDecl):
                yield d

    def theorems(self) -> Iterator[TheoremDecl]:
        for d in self.decls:
            if isinstance(d, TheoremDecl):
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

    def resolve(self) -> None:
        self.scope = scope = Scope[InferenceSort]()

        for s in self.sorts():
            s.resolve(scope)

        for rcf in self.relations_constants_and_functions():
            rcf.resolve(scope)

        for d in self.decls_containing_exprs():
            d.resolve(scope)

        for tr in self.traces():
            tr.resolve(scope)

        automata = list(self.automata())
        if len(automata) > 1:
            utils.print_error(automata[1].tok, 'at most one automaton may be declared (first was declared at %s)' % (
                utils.tok_to_string(automata[0].tok)
            ))

        if len(automata) > 0:
            a = automata[0]
            a.resolve(scope)

        assert len(scope.stack) == 0

    def __repr__(self) -> str:
        return 'Program(decls=%s)' % (self.decls,)

    def __str__(self) -> str:
        return '\n'.join(str(d) for d in self.decls)
