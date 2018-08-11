from contextlib import contextmanager
import itertools
import logging
import ply, ply.lex, ply.yacc
import sys
from typing import List, Union, Tuple, Optional, Dict, Iterator, \
    Callable, Any, NoReturn, Set
from typing_extensions import Protocol
import z3

Token = ply.lex.LexToken

def error(tok: Optional[Token], msg: str) -> NoReturn:
    raise Exception('%s: %s' %
                    ('%s:%s:%s' % (tok.filename, tok.lineno, tok.col)
                     if tok is not None else 'None', msg))

class Sort(object):
    def __repr__(self) -> str:
        raise Exception('Unexpected sort %s does not implement __repr__ method' % type(self))

    def __str__(self) -> str:
        raise Exception('Unexpected sort %s does not implement __str__ method' % repr(self))

    def resolve(self, scope: 'Scope') -> None:
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
    sort: 'InferenceSort'

class SortInferencePlaceholder(object):
    def __init__(self, d: Optional[HasSortField]=None) -> None:
        self.backpatches: List[HasSortField] = []
        if d is not None:
            self.add(d)

    def add(self, d: HasSortField) -> None:
        self.backpatches.append(d)

    def solve(self, sort: Sort) -> None:
        for d in self.backpatches:
            d.sort = sort

    def merge(self, other: 'SortInferencePlaceholder') -> None:
        for d in other.backpatches:
            assert d.sort is other
            d.sort = self
            self.backpatches.append(d)

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

class Expr(object):
    def __repr__(self) -> str:
        raise Exception('Unexpected expr %s does not implement __repr__ method' % type(self))

    def __str__(self) -> str:
        buf: List[str] = []
        self.pretty(buf, PREC_TOP, 'NONE')
        return ''.join(buf)

    def resolve(self, scope: 'Scope', sort: InferenceSort) -> InferenceSort:
        raise Exception('Unexpected expression %s does not implement resolve method' %
                        repr(self))

    def to_z3(self, key=None, key_old=None, old=False):
        # type: (Optional[str], Optional[str], bool) -> z3.ExprRef
        raise Exception('Unexpected expression %s does not implement to_z3 method' % repr(self))

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
        self.z3: Optional[z3.ExprRef] = None

    def __repr__(self) -> str:
        return 'true' if self.val else 'false'

    def _denote(self) -> object:
        return self.val

    def prec(self) -> int:
        return PREC_BOT

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        buf.append(str(self.val))

    def resolve(self, scope: 'Scope', sort: InferenceSort) -> InferenceSort:
        check_constraint(self.tok, sort, BoolSort)
        return BoolSort

    def to_z3(self, key=None, key_old=None, old=False):
        # type: (Optional[str], Optional[str], bool) -> z3.ExprRef
        if self.z3 is None:
            self.z3 = z3.BoolVal(self.val)
        return self.z3

    def free_ids(self) -> List[str]:
        return []

UNOPS = {
    'NOT',
    'OLD'
}
z3_UNOPS: Dict[str, Optional[Callable[[z3.ExprRef], z3.ExprRef]]] = {
    'NOT': z3.Not,
    'OLD': None
}

def check_constraint(tok: Optional[Token], expected: InferenceSort, actual: InferenceSort) -> None:
    if expected is None or actual is None:
        pass
    elif isinstance(expected, Sort):
        if isinstance(actual, Sort):
            if expected != actual:
                error(tok, 'expected sort %s but got %s' % (expected, actual))
        else:
            actual.solve(expected)
    else:
        if isinstance(actual, Sort):
            expected.solve(actual)
        else:
            expected.merge(actual)


class UnaryExpr(Expr):
    def __init__(self, tok: Optional[Token], op: str, arg: Expr) -> None:
        assert op in UNOPS
        self.tok = tok
        self.op = op
        self.arg = arg
        self.z3: Dict[Tuple[Optional[str], Optional[str], bool], z3.ExprRef] = {}

    def resolve(self, scope: 'Scope', sort: InferenceSort) -> InferenceSort:
        if self.op == 'OLD':
            return self.arg.resolve(scope, sort)
        else:
            assert self.op == 'NOT'
            check_constraint(self.tok, sort, BoolSort)
            self.arg.resolve(scope, BoolSort)
            return BoolSort

    def _denote(self) -> object:
        return (UnaryExpr, self.op, self.arg)

    def __repr__(self) -> str:
        return 'UnaryExpr(%s, %s)' % (self.op, repr(self.arg))

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

    def to_z3(self, key=None, key_old=None, old=False):
        # type: (Optional[str], Optional[str], bool) -> z3.ExprRef
        t = (key, key_old, old)
        if t not in self.z3:
            if self.op == 'OLD':
                assert not old and key_old is not None
                self.z3[t] = self.arg.to_z3(key, key_old, True)
            else:
                f = z3_UNOPS[self.op]
                assert f is not None
                self.z3[t] = f(self.arg.to_z3(key, key_old, old))
        return self.z3[t]

    def free_ids(self) -> List[str]:
        return self.arg.free_ids()

def Not(e: Expr) -> Expr:
    return UnaryExpr(None, 'NOT', e)

BINOPS = {
    'AND',
    'OR',
    'IMPLIES',
    'IFF',
    'EQUAL',
    'NOTEQ'
}
z3_BINOPS: Dict[str, Callable[[z3.ExprRef, z3.ExprRef], z3.ExprRef]] = {
    'AND' : z3.And,
    'OR' : z3.Or,
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
        self.z3: Dict[Tuple[Optional[str], Optional[str], bool], z3.ExprRef] = {}

    def resolve(self, scope: 'Scope', sort: InferenceSort) -> InferenceSort:
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
        return 'BinaryExpr(%s, %s, %s)' % (self.op,
                                           repr(self.arg1),
                                           repr(self.arg2))

    def prec(self) -> int:
        if self.op == 'AND':
            return PREC_AND
        elif self.op == 'OR':
            return PREC_OR
        elif self.op == 'IMPLIES':
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

        if self.op == 'AND':
            s = '&'
        elif self.op == 'OR':
            s = '|'
        elif self.op == 'IMPLIES':
            s = '->'
        elif self.op == 'IFF':
            s = '<->'
        elif self.op == 'EQUAL':
            s = '='
        elif self.op == 'NOTEQ':
            s = '!='
        else:
            assert False

        buf.append(' ')
        buf.append(s)
        buf.append(' ')

        self.arg2.pretty(buf, p, 'RIGHT')


    def to_z3(self, key=None, key_old=None, old=False):
        # type: (Optional[str], Optional[str], bool) -> z3.ExprRef
        t = (key, key_old, old)
        if t not in self.z3:
            self.z3[t] = z3_BINOPS[self.op](self.arg1.to_z3(key, key_old, old), self.arg2.to_z3(key, key_old, old))
        return self.z3[t]

    def free_ids(self) -> List[str]:
        x = self.arg1.free_ids()
        s = set(x)
        return x + [y for y in self.arg2.free_ids() if y not in s]


def And(*args: Expr) -> Expr:
    if len(args) == 0:
        return Bool(None, True)

    ans = args[0]
    for e in args[1:]:
        ans = BinaryExpr(None, 'AND', ans, e)

    return ans

def Eq(arg1: Expr, arg2: Expr) -> Expr:
    return BinaryExpr(None, 'EQUAL', arg1, arg2)

def Neq(arg1: Expr, arg2: Expr) -> Expr:
    return BinaryExpr(None, 'NOTEQ', arg1, arg2)

class AppExpr(Expr):
    def __init__(self, tok: Optional[Token], rel: str, args: List[Expr]) -> None:
        self.tok = tok
        self.rel = rel
        self.args = args
        self.decl: Optional[RelationDecl] = None
        self.z3: Dict[Tuple[Optional[str], Optional[str], bool], z3.ExprRef] = {}

    def resolve(self, scope: 'Scope', sort: InferenceSort) -> InferenceSort:
        d, _ = scope.get(self.rel)
        if d is None:
            error(self.tok, 'Unresolved relation name %s' % self.rel)

        assert isinstance(d, RelationDecl)
        self.decl = d

        check_constraint(self.tok, sort, BoolSort)

        for (arg, s) in zip(self.args, self.decl.arity):
            arg.resolve(scope, s)

        return BoolSort

    def _denote(self) -> object:
        assert self.decl is not None
        return (AppExpr, self.decl, tuple(self.args))

    def __repr__(self) -> str:
        return 'AppExpr(%s, %s)' % (self.rel, self.args)

    def prec(self) -> int:
        return PREC_BOT

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        buf.append(self.rel)
        buf.append('(')
        started = False
        for arg in self.args:
            if started:
                buf.append(', ')
            started = True
            arg.pretty(buf, PREC_TOP, 'NONE')
        buf.append(')')

    def to_z3(self, key=None, key_old=None, old=False):
        # type: (Optional[str], Optional[str], bool) -> z3.ExprRef
        assert self.decl is not None

        t = (key, key_old, old)
        if t not in self.z3:
            if not old:
                k = key
            else:
                assert key_old is not None
                k = key_old
            R = self.decl.to_z3(k)
            assert isinstance(R, z3.FuncDeclRef)
            self.z3[t] = R(*(arg.to_z3(key, key_old, old) for arg in self.args))
        return self.z3[t]

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

    def resolve(self, scope: 'Scope') -> None:
        if self.sort is None:
            error(self.tok, 'type annotation required for variable %s' % (self.name,))

        assert not isinstance(self.sort, SortInferencePlaceholder)

        self.sort.resolve(scope)

    def __repr__(self) -> str:
        return 'SortedVar(%s, %s)' % (self.name, repr(self.sort))

    def __str__(self) -> str:
        if self.sort is None:
            return self.name
        else:
            return '%s:%s' % (self.name, self.sort)


class QuantifierExpr(Expr):
    def __init__(self, tok: Optional[Token], quant: str, vs: List[SortedVar], body: Expr) -> None:
        assert quant in ['FORALL', 'EXISTS']
        assert len(vs) > 0
        self.tok = tok
        self.quant = quant
        self.vs = vs
        self.body = body
        self.binders: Dict[str, z3.ExprRef] = {}
        self.z3: Dict[Tuple[Optional[str], Optional[str], bool], z3.ExprRef] = {}

    def resolve(self, scope: 'Scope', sort: InferenceSort) -> InferenceSort:
        check_constraint(self.tok, sort, BoolSort)

        for sv in self.vs:
            if sv.sort is None:
                sv.sort = SortInferencePlaceholder(sv)
            else:
                assert not isinstance(sv.sort, SortInferencePlaceholder)
                sv.sort.resolve(scope)

        with scope.in_scope(self.vs, self):
            self.body.resolve(scope, BoolSort)

        for sv in self.vs:
            if isinstance(sv.sort, SortInferencePlaceholder):
                error(sv.tok, 'Could not infer sort for variable %s' % (sv.name,))

        return BoolSort

    def __repr__(self) -> str:
        return 'QuantifierExpr@%s(%s, %s, %s)' % (id(self), self.quant, self.vs, repr(self.body))

    def _denote(self) -> object:
        return (QuantifierExpr, self.quant, self.body)

    def prec(self) -> int:
        return PREC_QUANT

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        buf.append(self.quant.lower())
        buf.append(' ')

        started = False
        for sv in self.vs:
            if started:
                buf.append(', ')
            started = True
            buf.append(str(sv))
        buf.append('. ')

        self.body.pretty(buf, PREC_QUANT, 'NONE')

    def to_z3(self, key=None, key_old=None, old=False):
        # type: (Optional[str], Optional[str], bool) -> z3.ExprRef
        t = (key, key_old, old)
        if t not in self.z3:
            bs = []
            for sv in self.vs:
                n = sv.name
                assert sv.sort is not None and not isinstance(sv.sort, SortInferencePlaceholder)
                self.binders[n] = z3.Const(n, sv.sort.to_z3())
                bs.append(self.binders[n])

            q = z3.ForAll if self.quant == 'FORALL' else z3.Exists

            self.z3[t] = q(bs, self.body.to_z3(key, key_old, old))
        return self.z3[t]

    def free_ids(self) -> List[str]:
        return [x for x in self.body.free_ids() if not any(v.name == x for v in self.vs)]

class Id(Expr):
    '''Unresolved symbol (might represent a constant or a variable)'''
    def __init__(self, tok: Optional[Token], name: str) -> None:
        self.tok = tok
        self.name = name
        self.decl: Optional[Binder] = None
        self.index: Optional[Tuple[int, int]] = None
        self.z3: Dict[Tuple[Optional[str], Optional[str], bool], z3.ExprRef] = {}

    def resolve(self, scope: 'Scope', sort: InferenceSort) -> InferenceSort:
        self.decl, x = scope.get(self.name)
        if self.decl is None:
            error(self.tok, 'Unresolved variable %s' % (self.name,))

        if isinstance(self.decl, QuantifierExpr):
            assert x is not None
            self.index = x

            for sv in self.decl.vs:
                if sv.name == self.name:
                    check_constraint(self.tok, sort, sv.sort)
                    return sv.sort
            assert False
        elif isinstance(self.decl, TransitionDecl):
            assert x is not None
            self.index = x

            for p in self.decl.params:
                if p.name == self.name:
                    check_constraint(self.tok, sort, p.sort)
                    return p.sort
            assert False
        elif isinstance(self.decl, RelationDecl):
            check_constraint(self.tok, sort, BoolSort)
            return BoolSort
        elif isinstance(self.decl, ConstantDecl):
            check_constraint(self.tok, sort, self.decl.sort)
            return self.decl.sort
        else:
            assert False


    def _denote(self) -> object:
        if self.index is not None:
            return (Id, self.index)
        else:
            assert self.decl is not None
            assert isinstance(self.decl, RelationDecl) or \
                isinstance(self.decl, ConstantDecl)
            return (Id, self.decl)

    def __repr__(self) -> str:
        return 'Id(%s, decl=%s)' % (self.name,
                                    id(self.decl) if self.decl is not None else 'None')

    def prec(self) -> int:
        return PREC_BOT

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        buf.append(self.name)

    def to_z3(self, key=None, key_old=None, old=False):
        # type: (Optional[str], Optional[str], bool) -> z3.ExprRef
        assert self.decl is not None

        t = (key, key_old, old)
        if t not in self.z3:
            if isinstance(self.decl, QuantifierExpr) or \
               isinstance(self.decl, TransitionDecl):
                self.z3[t] = self.decl.binders[self.name]
            elif isinstance(self.decl, RelationDecl) or \
                 isinstance(self.decl, ConstantDecl):
                if not old:
                    k = key
                else:
                    assert not self.decl.mutable or key_old is not None
                    k = key_old
                x = self.decl.to_z3(k)
                assert isinstance(x, z3.ExprRef)
                self.z3[t] = x
            else:
                raise Exception('Unsupported binding declaration %s' % repr(self.decl))
        return self.z3[t]

    def free_ids(self) -> List[str]:
        return [self.name]

Arity = List[Sort]

class UninterpretedSort(Sort):
    def __init__(self, tok: Optional[Token], name: str) -> None:
        self.tok = tok
        self.name = name
        self.decl: Optional[SortDecl] = None

    def resolve(self, scope: 'Scope') -> None:
        self.decl = scope.get_sort(self.name)
        if self.decl is None:
            error(self.tok, 'Unresolved sort name %s' % (self.name,))

    def __repr__(self) -> str:
        return 'UninterpretedSort(%s)' % (self.name,)

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

    def resolve(self, scope: 'Scope') -> None:
        pass

    def to_z3(self) -> z3.SortRef:
        return z3.BoolSort()

    def _denote(self) -> object:
        return _BoolSort

BoolSort = _BoolSort()

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

    def resolve(self, scope: 'Scope') -> None:
        scope.add_sort(self.tok, self.name, self)

    def __repr__(self) -> str:
        return 'SortDecl(%s)' % self.name

    def __str__(self) -> str:
        return 'sort %s' % self.name

    def to_z3(self) -> z3.SortRef:
        if self.z3 is None:
            self.z3 = z3.DeclareSort(self.name)

        return self.z3

class RelationDecl(Decl):
    def __init__(self, tok: Optional[Token], name: str, arity: Arity, mutable: bool) -> None:
        self.tok = tok
        self.name = name
        self.arity = arity
        self.mutable = mutable
        self.mut_z3: Dict[str, Union[z3.FuncDeclRef, z3.ExprRef]] = {}
        self.immut_z3: Optional[Union[z3.FuncDeclRef, z3.ExprRef]] = None

    def resolve(self, scope: 'Scope') -> None:
        for sort in self.arity:
            sort.resolve(scope)

        scope.add_relation(self.tok, self.name, self)

    def __repr__(self) -> str:
        return 'RelationDecl(%s, %s, mutable=%s)' % (self.name, self.arity, self.mutable)

    def __str__(self) -> str:
        return '%s relation %s(%s)' % ('mutable' if self.mutable else 'immutable',
                                       self.name,
                                       ', '.join([str(s) for s in self.arity]))

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


class ConstantDecl(Decl):
    def __init__(self, tok: Optional[Token], name: str, sort: Sort, mutable: bool) -> None:
        self.tok = tok
        self.name = name
        self.sort = sort
        self.mutable = mutable
        self.mut_z3: Dict[str, z3.ExprRef] = {}
        self.immut_z3: Optional[z3.ExprRef] = None


    def __repr__(self) -> str:
        return 'ConstantDecl(%s, %s, mutable=%s)' % (self.name, self.sort, self.mutable)

    def __str__(self) -> str:
        return '%s constant %s: %s' % ('mutable' if self.mutable else 'immutable',
                                       self.name, self.sort)

    def resolve(self, scope: 'Scope') -> None:
        self.sort.resolve(scope)
        scope.add_constant(self.tok, self.name, self)

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

def close_free_vars(expr: Expr, in_scope: List[str]=[]) -> Expr:
    vs = [s for s in expr.free_ids() if s not in in_scope and s.isupper()]
    if vs == []:
        return expr
    else:
        logging.debug('closing expression')
        logging.debug(str(expr))
        logging.debug('with free vars %s' % vs)
        return QuantifierExpr(None, 'FORALL', [SortedVar(None, v, None) for v in vs], expr)

class InitDecl(Decl):
    def __init__(self, tok: Optional[Token], name: Optional[str], expr: Expr) -> None:
        self.tok = tok
        self.name = name
        self.expr = expr

    def resolve(self, scope: 'Scope') -> None:
        self.expr = close_free_vars(self.expr)
        self.expr.resolve(scope, BoolSort)


    def __repr__(self) -> str:
        return 'InitDecl(%s, %s)' % (self.name if self.name is not None else 'None',
                                     repr(self.expr))

    def __str__(self) -> str:
        return 'init %s%s' % (('[%s] ' % self.name) if self.name is not None else '',
                              self.expr)

class ModifiesClause(object):
    def __init__(self, tok: Optional[Token], name: str) -> None:
        self.tok = tok
        self.name = name
        self.decl: Optional[Binder] = None

    def resolve(self, scope: 'Scope') -> None:
        self.decl, _ = scope.get(self.name)

        if self.decl is None:
            error(self.tok, 'Unresolved constant or relation %s' % (self.name,))

    def __repr__(self) -> str:
        return 'ModifiesClause(%s, %s)' % (self.name, repr(self.decl))

    def __str__(self) -> str:
        return self.name

class TransitionDecl(Decl):
    def __init__(self, tok: Optional[Token], name: str, params: List[SortedVar],
                 mods: List[ModifiesClause], expr: Expr) -> None:
        self.tok = tok
        self.name = name
        self.params = params
        self.mods = mods
        self.expr = expr

        self.scope: Optional[Scope] = None

        self.binders: Dict[str, z3.ExprRef] = {}
        self.z3: Dict[Tuple[str, str], z3.ExprRef] = {}

    def resolve(self, scope: 'Scope') -> None:
        assert len(scope.stack) == 0

        self.scope = scope

        for param in self.params:
            param.resolve(scope)

        for mod in self.mods:
            mod.resolve(scope)

        self.expr = close_free_vars(self.expr, in_scope=[p.name for p in self.params])

        with scope.in_scope(self.params, self):
            self.expr.resolve(scope, BoolSort)

    def __repr__(self) -> str:
        return 'TransitionDecl(%s, %s, %s, %s)' % (self.name, self.params,
                                                   self.mods, repr(self.expr))

    def __str__(self) -> str:
        return 'transition %s(%s)\n  modifies %s\n  %s' % \
            (self.name,
             ', '.join([str(p) for p in self.params]),
             ', '.join([str(m) for m in self.mods]),
             self.expr)

    def to_z3(self, key: str, key_old: str) -> z3.ExprRef:
        assert self.scope is not None

        t = (key, key_old)
        if t not in self.z3:

            bs = []
            for p in self.params:
                n = p.name
                assert p.sort is not None and not isinstance(p.sort, SortInferencePlaceholder)
                self.binders[n] = z3.Const(n, p.sort.to_z3())
                bs.append(self.binders[n])

            mods = []
            R: Iterator[Union[RelationDecl, ConstantDecl]] = iter(self.scope.relations.values())
            C: Iterator[Union[RelationDecl, ConstantDecl]] = iter(self.scope.constants.values())
            for d in itertools.chain(R, C):
                if not d.mutable or any(mc.decl == d for mc in self.mods):
                    continue

                if isinstance(d, ConstantDecl) or len(d.arity) == 0:
                    lhs = d.to_z3(key)
                    rhs = d.to_z3(key_old)
                    assert isinstance(lhs, z3.ExprRef) and isinstance(rhs, z3.ExprRef)
                    e = lhs == rhs
                else:
                    cs: List[z3.ExprRef] = []
                    i = 0
                    for s in d.arity:
                        cs.append(z3.Const('x' + str(i), s.to_z3()))
                        i += 1

                    lhs = d.to_z3(key)
                    rhs = d.to_z3(key_old)
                    assert isinstance(lhs, z3.FuncDeclRef) and isinstance(rhs, z3.FuncDeclRef)


                    e = z3.Forall(cs, lhs(*cs) == rhs(*cs))


                mods.append(e)

            self.z3[t] = z3.Exists(bs, z3.And(self.expr.to_z3(key, key_old), *mods))

        return self.z3[t]

class InvariantDecl(Decl):
    def __init__(self, tok: Optional[Token], name: Optional[str], expr: Expr) -> None:
        self.tok = tok
        self.name = name
        self.expr = expr

    def resolve(self, scope: 'Scope') -> None:
        self.expr = close_free_vars(self.expr)
        self.expr.resolve(scope, BoolSort)

    def __repr__(self) -> str:
        return 'InvariantDecl(%s, %s)' % (self.name if self.name is not None else 'None',
                                          repr(self.expr))

    def __str__(self) -> str:
        return 'invariant %s%s' % (('[%s] ' % self.name) if self.name is not None else '',
                                   self.expr)


class AxiomDecl(Decl):
    def __init__(self, tok: Optional[Token], name: Optional[str], expr: Expr) -> None:
        self.tok = tok
        self.name = name
        self.expr = expr

    def resolve(self, scope: 'Scope') -> None:
        self.expr.resolve(scope, BoolSort)

    def __repr__(self) -> str:
        self.expr = close_free_vars(self.expr)
        return 'AxiomDecl(%s, %s)' % (self.name if self.name is not None else 'None',
                                      repr(self.expr))

    def __str__(self) -> str:
        return 'axiom %s%s' % (('[%s] ' % self.name) if self.name is not None else '',
                               self.expr)


Binder = Union[RelationDecl, ConstantDecl, TransitionDecl, QuantifierExpr]

class Scope:
    def __init__(self) -> None:
        self.stack: List[Tuple[List[SortedVar], Binder]] = []
        self.sorts: Dict[str, SortDecl] = {}
        self.relations: Dict[str, RelationDecl] = {}
        self.constants: Dict[str, ConstantDecl] = {}

    def push(self, vs: List[SortedVar], binder: Binder) -> None:
        self.stack.append((vs, binder))

    def pop(self) -> None:
        self.stack.pop()

    def get(self, name: str) -> Tuple[Optional[Binder], Optional[Tuple[int, int]]]:
        # first, check for bound variables in scope
        for i, (vs, binder) in enumerate(reversed(self.stack)):
            for j, v in enumerate(vs):
                if v.name == name:
                    return (binder, (i, j))

        # otherwise, check for constants/relations (whose domains are disjoint)
        d = self.constants.get(name) or self.relations.get(name)
        return (d, None)

    def add_constant(self, tok: Optional[Token], constant: str, decl: ConstantDecl) -> None:
        assert len(self.stack) == 0

        if constant in self.constants:
            error(tok, 'Duplicate constant name %s' % (constant,))

        if constant in self.relations:
            error(tok, 'Constant name %s is already declared as a relation' %
                  (constant,))

        self.constants[constant] = decl

    def add_sort(self, tok: Optional[Token], sort: str, decl: SortDecl) -> None:
        assert len(self.stack) == 0

        if sort in self.sorts:
            error(tok, 'Duplicate sort name %s' % (sort,))

        self.sorts[sort] = decl

    def get_sort(self, sort: str) -> Optional[SortDecl]:
        return self.sorts.get(sort)

    def add_relation(self, tok: Optional[Token], relation: str, decl: RelationDecl) -> None:
        assert len(self.stack) == 0

        if relation in self.relations:
            error(tok, 'Duplicate relation name %s' % (relation,))

        if relation in self.constants:
            error(tok, 'Relation name %s is already declared as a constant' % (relation,))

        self.relations[relation] = decl

    @contextmanager
    def in_scope(self, vs: List[SortedVar], binder: Binder) -> Iterator[None]:
        n = len(self.stack)
        self.push(vs, binder)
        yield
        self.pop()
        assert n == len(self.stack)

class Program(object):
    def __init__(self, decls: List[Decl]) -> None:
        self.decls = decls
        self.scope: Optional[Scope] = None

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

    def transitions(self) -> Iterator[TransitionDecl]:
        for d in self.decls:
            if isinstance(d, TransitionDecl):
                yield d

    def axioms(self) -> Iterator[AxiomDecl]:
        for d in self.decls:
            if isinstance(d, AxiomDecl):
                yield d

    def relations_and_constants(self) -> Iterator[Union[RelationDecl, ConstantDecl]]:
        for d in self.decls:
            if isinstance(d, RelationDecl) or \
               isinstance(d, ConstantDecl):
                yield d

    def decls_containing_exprs(self)\
        -> Iterator[Union[InitDecl, TransitionDecl, InvariantDecl, AxiomDecl]]:
        for d in self.decls:
            if isinstance(d, InitDecl) or \
               isinstance(d, TransitionDecl) or \
               isinstance(d, InvariantDecl) or \
               isinstance(d, AxiomDecl):
                yield d

    def resolve(self) -> None:
        self.scope = scope = Scope()

        for s in self.sorts():
            s.resolve(scope)

        for rc in self.relations_and_constants():
            rc.resolve(scope)

        for d in self.decls_containing_exprs():
            d.resolve(scope)

        assert len(scope.stack) == 0

    def __repr__(self) -> str:
        return 'Program(%s)' % (self.decls,)

    def __str__(self) -> str:
        return '\n'.join(str(d) for d in self.decls)
            
