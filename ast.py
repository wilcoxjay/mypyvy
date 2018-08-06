import ply
import ply.lex
import ply.yacc

import z3
from typing import List, Union, Tuple, Optional, Dict, Iterator, Callable, Any, NoReturn, Set
import sys
import logging
try:
    from typing_extensions import Protocol
except Exception:
    Protocol = object # type: ignore

from contextlib import contextmanager

Token = ply.lex.LexToken

def error(tok, msg): # type: (Optional[Token], str) -> NoReturn
    raise Exception('%s: %s' %
                    ('%s:%s:%s' % (tok.filename, tok.lineno, tok.col)
                     if tok is not None else 'None', msg))

class Sort(object):
    def __repr__(self): # type: () -> str
        raise Exception('Unexpected sort %s does not implement __repr__ method' % type(self))

    def __str__(self): # type: () -> str
        raise Exception('Unexpected sort %s does not implement __str__ method' % repr(self))

    def resolve(self, scope): # type: (Scope) -> None
        raise Exception('Unexpected sort %s does not implement resolve method' % repr(self))

    def to_z3(self): # type: () -> z3.SortRef
        raise Exception('Unexpected sort %s does not implement to_z3 method' % repr(self))

    def __eq__(self, other): # type: (object) -> bool
        raise Exception('Unexpected sort %s does not implement __eq__ method' % repr(self))

    def __ne__(self, other): # type: (object) -> bool
        raise Exception('Unexpected sort %s does not implement __ne__ method' % repr(self))



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

def no_parens(ip, op, side): # type: (int, int, str) -> bool
    return ip < op or (ip == op and side == PREC_ASSOC[ip])

class Expr(object):
    def __repr__(self): # type: () -> str
        raise Exception('Unexpected expr %s does not implement __repr__ method' % type(self))

    def __str__(self): # type: () -> str
        buf = [] # type: List[str]
        self.pretty(buf, PREC_TOP, 'NONE')
        return ''.join(buf)

    def resolve(self, scope, sort): # type: (Scope, InferenceSort) -> InferenceSort
        raise Exception('Unexpected expression %s does not implement resolve method' % repr(self))

    def to_z3(self, key=None, key_old=None, old=False):
        # type: (Optional[str], Optional[str], bool) -> z3.ExprRef
        raise Exception('Unexpected expression %s does not implement to_z3 method' % repr(self))

    def __eq__(self, other): # type: (object) -> bool
        raise Exception('Unexpected expr %s does not implement __eq__ method' % repr(self))

    def __ne__(self, other): # type: (object) -> bool
        raise Exception('Unexpected expr %s does not implement __ne__ method' % repr(self))

    def pretty(self, buf, prec, side): # type: (List[str], int, str) -> None
        needs_parens = not no_parens(self.prec(), prec, side)

        if needs_parens:
            buf.append('(')
            prec = PREC_TOP
            side = 'NONE'

        self._pretty(buf, prec, side)

        if needs_parens:
            buf.append(')')

    def prec(self): # type: () -> int
        raise Exception('Unexpected expr %s does not implement prec method' % repr(self))

    def _pretty(self, buf, prec, side): # type: (List[str], int, str) -> None
        raise Exception('Unexpected expr %s does not implement pretty method' % repr(self))

    def free_ids(self): # type: () -> Set[str]
        raise Exception('Unexpected expr %s does not implement contains_var method' % repr(self))


class Bool(Expr):
    def __init__(self, tok, val): # type: (Optional[Token], bool) -> None
        self.tok = tok
        self.val = val

    def __repr__(self):
        return 'true' if self.val else 'false'

    def prec(self): # type: () -> int
        return PREC_BOT

    def _pretty(self, buf, prec, side): # type: (List[str], int, str) -> None
        buf.append(str(self.val))

    def resolve(self, scope, sort): # type: (Scope, InferenceSort) -> InferenceSort
        check_constraint(self.tok, sort, BoolSort)
        return BoolSort

    def to_z3(self, key=None, key_old=None, old=False):
        # type: (Optional[str], Optional[str], bool) -> z3.ExprRef

        return z3.BoolVal(self.val)

    def __eq__(self, other): # type: (object) -> bool
        return isinstance(other, Bool) and other.val == self.val

    def __ne__(self, other): # type: (object) -> bool
        return not (self == other)

    def free_ids(self): # type: () -> Set[str]
        return set()

UNOPS = set([
    'NOT',
    'OLD'
])
z3_UNOPS = {
    'NOT': z3.Not,
    'OLD': None
} # type: Any
# Dict[str, Callable[[z3.ExprRef], z3.ExprRef]]

def check_constraint(tok, expected, actual):
    # type: (Optional[Token], InferenceSort, InferenceSort) -> None
    if expected is None:
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
    def __init__(self, tok, op, arg): # type: (Optional[Token], str, Expr) -> None
        assert op in UNOPS
        self.tok = tok
        self.op = op
        self.arg = arg

    def resolve(self, scope, sort): # type: (Scope, InferenceSort) -> InferenceSort
        if self.op == 'OLD':
            return self.arg.resolve(scope, sort)
        else:
            assert self.op == 'NOT'
            check_constraint(self.tok, sort, BoolSort)
            self.arg.resolve(scope, BoolSort)
            return BoolSort

    def __repr__(self): # type: () -> str
        return 'UnaryExpr(%s, %s)' % (self.op, repr(self.arg))

    def prec(self): # type: () -> int
        if self.op == 'NOT':
            return PREC_NOT
        elif self.op == 'OLD':
            return PREC_BOT
        else:
            assert False

    def _pretty(self, buf, prec, side): # type: (List[str], int, str) -> None
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
        if self.op == 'OLD':
            assert not old and key_old is not None
            return self.arg.to_z3(key, key_old, True)
        else:
            return z3_UNOPS[self.op](self.arg.to_z3(key, key_old, old))

    def free_ids(self): # type: () -> Set[str]
        return self.arg.free_ids()

def Not(e): # type: (Expr) -> Expr
    return UnaryExpr(None, 'NOT', e)

BINOPS = set([
    'AND',
    'OR',
    'IMPLIES',
    'IFF',
    'EQUAL',
    'NOTEQ'
])
z3_BINOPS = {
    'AND' : z3.And,
    'OR' : z3.Or,
    'IMPLIES' : z3.Implies,
    'IFF' : lambda x, y: x == y,
    'EQUAL' : lambda x, y: x == y,
    'NOTEQ' : lambda x, y: x != y
} # type: Dict[str, Callable[[z3.ExprRef, z3.ExprRef], z3.ExprRef]]

class BinaryExpr(Expr):
    def __init__(self, tok, op, arg1, arg2): # type: (Optional[Token], str, Expr, Expr) -> None
        assert op in BINOPS
        self.tok = tok
        self.op = op
        self.arg1 = arg1
        self.arg2 = arg2

    def resolve(self, scope, sort): # type: (Scope, InferenceSort) -> InferenceSort
        check_constraint(self.tok, sort, BoolSort)

        if self.op in ['AND', 'OR', 'IMPLIES', 'IFF']:
            self.arg1.resolve(scope, BoolSort)
            self.arg2.resolve(scope, BoolSort)
        else:
            assert self.op in ['EQUAL', 'NOTEQ']
            s = self.arg1.resolve(scope, None)
            self.arg2.resolve(scope, s)

        return BoolSort


    def __repr__(self): # type: () -> str
        return 'BinaryExpr(%s, %s, %s)' % (self.op,
                                           repr(self.arg1),
                                           repr(self.arg2))

    def prec(self): # type: () -> int
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

    def _pretty(self, buf, prec, side): # type: (List[str], int, str) -> None
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
        return z3_BINOPS[self.op](self.arg1.to_z3(key, key_old, old), self.arg2.to_z3(key, key_old, old))

    def free_ids(self): # type: () -> Set[str]
        return self.arg1.free_ids() | self.arg2.free_ids()


def And(*args): # type: (*Expr) -> Expr
    if len(args) == 0:
        return Bool(None, True)

    ans = args[0]
    for e in args[1:]:
        ans = BinaryExpr(None, 'AND', ans, e)

    return ans

def Eq(arg1, arg2): # type: (Expr, Expr) -> Expr
    return BinaryExpr(None, 'EQUAL', arg1, arg2)

def Neq(arg1, arg2): # type: (Expr, Expr) -> Expr
    return BinaryExpr(None, 'NOTEQ', arg1, arg2)

class AppExpr(Expr):
    def __init__(self, tok, rel, args): # type: (Optional[Token], str, List[Expr]) -> None
        self.tok = tok
        self.rel = rel
        self.args = args
        self.decl = None # type: Optional[RelationDecl]

    def resolve(self, scope, sort): # type: (Scope, InferenceSort) -> InferenceSort
        d = scope.get(self.rel)
        if d is None:
            error(self.tok, 'Unresolved relation name %s' % self.rel)

        assert isinstance(d, RelationDecl)
        self.decl = d

        check_constraint(self.tok, sort, BoolSort)

        for (arg, s) in zip(self.args, self.decl.arity):
            arg.resolve(scope, s)

        return BoolSort

    def __repr__(self): # type: () -> str
        return 'AppExpr(%s, %s)' % (self.rel, self.args)

    def prec(self): # type: () -> int
        return PREC_BOT

    def _pretty(self, buf, prec, side): # type: (List[str], int, str) -> None
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

        if not old:
            k = key
        else:
            assert key_old is not None
            k = key_old
        R = self.decl.to_z3(k)
        assert isinstance(R, z3.FuncDeclRef)
        return R(*(arg.to_z3(key, key_old, old) for arg in self.args))

    def free_ids(self): # type: () -> Set[str]
        ans = set() # type: Set[str]
        return ans.union(*[arg.free_ids() for arg in self.args])

class SortedVar(object):
    def __init__(self, tok, name, sort): # type: (Optional[Token], str, Optional[Sort]) -> None
        self.tok = tok
        self.name = name
        self.sort = sort # type: InferenceSort

    def resolve(self, scope): # type: (Scope) -> None
        if self.sort is None:
            error(self.tok, 'type annotation required for variable %s' % (self.name,))

        assert not isinstance(self.sort, SortInferencePlaceholder)

        self.sort.resolve(scope)

    def __repr__(self): # type: () -> str
        return 'SortedVar(%s, %s)' % (self.name, repr(self.sort))

    def __str__(self): # type: () -> str
        if self.sort is None:
            return self.name
        else:
            return '%s:%s' % (self.name, self.sort)

class HasSortField(Protocol):
    sort = None # type: InferenceSort

class SortInferencePlaceholder(object):
    def __init__(self, d=None):
        self.backpatches = [] # type: List[HasSortField]
        if d is not None:
            self.add(d)

    def add(self, d): # type: (HasSortField) -> None
        self.backpatches.append(d)

    def solve(self, sort): # type: (Sort) -> None
        for d in self.backpatches:
            d.sort = sort

    def merge(self, other): # type: (SortInferencePlaceholder) -> None
        for d in other.backpatches:
            assert d.sort is other
            d.sort = self
            self.backpatches.append(d)

InferenceSort = Union[Sort, SortInferencePlaceholder, None]

class QuantifierExpr(Expr):
    def __init__(self, tok, quant, vs, body): # type: (Optional[Token], str, List[SortedVar], Expr) -> None
        assert quant in ['FORALL', 'EXISTS']
        assert len(vs) > 0
        self.tok = tok
        self.quant = quant
        self.vs = vs
        self.body = body
        self.binders = {} # type: Dict[str, z3.ExprRef]

    def resolve(self, scope, sort): # type: (Scope, InferenceSort) -> InferenceSort
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

    def __repr__(self): # type: () -> str
        return 'QuantifierExpr@%s(%s, %s, %s)' % (id(self), self.quant, self.vs, repr(self.body))

    def prec(self): # type: () -> int
        return PREC_QUANT

    def _pretty(self, buf, prec, side): # type: (List[str], int, str) -> None
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
        bs = []
        for sv in self.vs:
            n = sv.name
            assert sv.sort is not None and not isinstance(sv.sort, SortInferencePlaceholder)
            self.binders[n] = z3.Const(n, sv.sort.to_z3())
            bs.append(self.binders[n])

        q = z3.ForAll if self.quant == 'FORALL' else z3.Exists

        return q(bs, self.body.to_z3(key, key_old, old))

    def free_ids(self): # type: () -> Set[str]
        return self.body.free_ids() - set([v.name for v in self.vs])

class Id(Expr):
    '''Unresolved symbol (might represent a constant or a variable)'''
    def __init__(self, tok, name): # type: (Optional[Token], str) -> None
        self.tok = tok
        self.name = name
        self.decl = None # type: Optional[Binder]

    def resolve(self, scope, sort): # type: (Scope, InferenceSort) -> InferenceSort
        self.decl = scope.get(self.name)
        if self.decl is None:
            error(self.tok, 'Unresolved variable %s' % (self.name,))

        if isinstance(self.decl, QuantifierExpr):
            for sv in self.decl.vs:
                if sv.name == self.name:
                    check_constraint(self.tok, sort, sv.sort)
                    return sv.sort
            assert False
        elif isinstance(self.decl, TransitionDecl):
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


    def __repr__(self): # type: () -> str
        return 'Id(%s, decl=%s)' % (self.name,
                                    id(self.decl) if self.decl is not None else 'None')

    def prec(self): # type: () -> int
        return PREC_BOT

    def _pretty(self, buf, prec, side): # type: (List[str], int, str) -> None
        buf.append(self.name)

    def to_z3(self, key=None, key_old=None, old=False):
        # type: (Optional[str], Optional[str], bool) -> z3.ExprRef
        assert self.decl is not None

        if isinstance(self.decl, QuantifierExpr) or \
           isinstance(self.decl, TransitionDecl):
            return self.decl.binders[self.name]
        elif isinstance(self.decl, RelationDecl) or \
             isinstance(self.decl, ConstantDecl):
            if not old:
                k = key
            else:
                assert not self.decl.mutable or key_old is not None
                k = key_old
            x = self.decl.to_z3(k)
            assert isinstance(x, z3.ExprRef)
            return x

        raise Exception('Unsupported binding declaration %s' % repr(self.decl))

    def free_ids(self): # type: () -> Set[str]
        return set([self.name])

Arity = List[Sort]

class UninterpretedSort(Sort):
    def __init__(self, tok, name): # type: (Optional[Token], str) -> None
        self.tok = tok
        self.name = name
        self.decl = None # type: Optional[SortDecl]

    def resolve(self, scope): # type: (Scope) -> None
        self.decl = scope.get_sort(self.name)
        if self.decl is None:
            error(self.tok, 'Unresolved sort name %s' % (self.name,))

    def __repr__(self): # type: () -> str
        return 'UninterpretedSort(%s)' % (self.name,)

    def __str__(self): # type: () -> str
        return self.name

    def to_z3(self): # type: () -> z3.SortRef
        assert self.decl is not None

        return self.decl.to_z3()

    def __eq__(self, other): # type: (object) -> bool
        return isinstance(other, UninterpretedSort) and \
            other.name == self.name

    def __ne__(self, other): # type: (object) -> bool
        return not (self == other)


class _BoolSort(Sort):
    def __repr__(self): # type: () -> str
        return 'bool'

    def __str__(self): # type: () -> str
        return 'bool'

    def resolve(self, scope): # type: (Scope) -> None
        pass

    def to_z3(self): # type: () -> z3.SortRef
        return z3.BoolSort()

    def __eq__(self, other): # type: (object) -> bool
        return isinstance(other, _BoolSort)

    def __ne__(self, other): # type: (object) -> bool
        return not (self == other)


BoolSort = _BoolSort()

class Decl(object):
    def __repr__(self): # type: () -> str
        raise Exception('Unexpected decl %s does not implement __repr__ method' % type(self))

    def __str__(self): # type: () -> str
        raise Exception('Unexpected decl %s does not implement __str__ method' % type(self))


class SortDecl(Decl):
    def __init__(self, tok, name): # type: (Token, str) -> None
        self.tok = tok
        self.name = name
        self.z3 = None # type: Optional[z3.SortRef]

    def resolve(self, scope): # type: (Scope) -> None
        scope.add_sort(self.tok, self.name, self)

    def __repr__(self): # type: () -> str
        return 'SortDecl(%s)' % self.name

    def __str__(self): # type: () -> str
        return 'sort %s' % self.name

    def to_z3(self): # type: () -> z3.SortRef
        if self.z3 is None:
            self.z3 = z3.DeclareSort(self.name)

        return self.z3

class RelationDecl(Decl):
    def __init__(self, tok, name, arity, mutable): # type: (Token, str, Arity, bool) -> None
        self.tok = tok
        self.name = name
        self.arity = arity
        self.mutable = mutable
        self.mut_z3 = {} # type: Dict[str, Union[z3.FuncDeclRef, z3.ExprRef]]
        self.immut_z3 = None # type: Optional[Union[z3.FuncDeclRef, z3.ExprRef]]

    def resolve(self, scope): # type: (Scope) -> None
        for sort in self.arity:
            sort.resolve(scope)

        scope.add_relation(self.tok, self.name, self)

    def __repr__(self): # type: () -> str
        return 'RelationDecl(%s, %s, mutable=%s)' % (self.name, self.arity, self.mutable)

    def __str__(self): # type: () -> str
        return '%s relation %s(%s)' % ('mutable' if self.mutable else 'immutable',
                                       self.name,
                                       ', '.join([str(s) for s in self.arity]))

    def to_z3(self, key): # type: (Optional[str]) -> Union[z3.FuncDeclRef, z3.ExprRef]
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
    def __init__(self, tok, name, sort, mutable): # type: (Token, str, Sort, bool) -> None
        self.tok = tok
        self.name = name
        self.sort = sort
        self.mutable = mutable
        self.mut_z3 = {} # type: Dict[str, z3.ExprRef]
        self.immut_z3 = None # type: Optional[z3.ExprRef]


    def __repr__(self): # type: () -> str
        return 'ConstantDecl(%s, %s, mutable=%s)' % (self.name, self.sort, self.mutable)

    def __str__(self): # type: () -> str
        return '%s constant %s: %s' % ('mutable' if self.mutable else 'immutable',
                                       self.name, self.sort)

    def resolve(self, scope): # type: (Scope) -> None
        self.sort.resolve(scope)
        scope.add_constant(self.tok, self.name, self)

    def to_z3(self, key): # type: (Optional[str]) -> z3.ExprRef
        if self.mutable:
            assert key is not None
            if key not in self.mut_z3:
                self.mut_z3[key] = z3.Const(key + '_' + self.name, self.sort.to_z3())

            return self.mut_z3[key]
        else:
            if self.immut_z3 is None:
                self.immut_z3 = z3.Const(self.name, self.sort.to_z3())

            return self.immut_z3

def close_free_vars(expr, in_scope=[]): # type: (Expr, List[str]) -> Expr
    vs = [s for s in (expr.free_ids() - set(in_scope)) if s.isupper()]
    if vs == []:
        return expr
    else:
        logging.debug('closing expression')
        logging.debug(str(expr))
        logging.debug('with free vars %s' % vs)
        return QuantifierExpr(None, 'FORALL', [SortedVar(None, v, None) for v in vs], expr)

class InitDecl(Decl):
    def __init__(self, tok, name, expr): # type: (Token, Optional[str], Expr) -> None
        self.tok = tok
        self.name = name
        self.expr = expr

    def resolve(self, scope): # type: (Scope) -> None
        self.expr = close_free_vars(self.expr)
        self.expr.resolve(scope, BoolSort)


    def __repr__(self): # type: () -> str
        return 'InitDecl(%s, %s)' % (self.name if self.name is not None else 'None',
                                     repr(self.expr))

    def __str__(self): # type: () -> str
        return 'init %s%s' % (('[%s] ' % self.name) if self.name is not None else '',
                              self.expr)

class ModifiesClause(object):
    def __init__(self, tok, name): # type: (Token, str) -> None
        self.tok = tok
        self.name = name
        self.decl = None # type: Optional[Binder]

    def resolve(self, scope): # type: (Scope) -> None
        self.decl = scope.get(self.name)

        if self.decl is None:
            error(self.tok, 'Unresolved constant or relation %s' % (self.name,))

    def __repr__(self): # type: () -> str
        return 'ModifiesClause(%s, %s)' % (self.name, repr(self.decl))

    def __str__(self): # type: () -> str
        return self.name

class TransitionDecl(Decl):
    def __init__(self, tok, name, params, mods, expr):
        # type: (Token, str, List[SortedVar], List[ModifiesClause], Expr) -> None
        self.tok = tok
        self.name = name
        self.params = params
        self.mods = mods
        self.expr = expr

        # The whole program containing this transition.
        # Filled out by resolution.
        # Useful when converting to z3, because we need to add "doesn't change"
        # conjuncts for every mutable relation/constant in the program that is
        # not in the modifies clause.
        self.prog = None # type: Optional[Program]

        self.binders = {} # type: Dict[str, z3.ExprRef]

    def resolve(self, scope): # type: (Scope) -> None
        assert len(scope.stack) == 0

        self.prog = scope.prog

        for param in self.params:
            param.resolve(scope)

        for mod in self.mods:
            mod.resolve(scope)

        self.expr = close_free_vars(self.expr, in_scope=[p.name for p in self.params])

        with scope.in_scope(self.params, self):
            self.expr.resolve(scope, BoolSort)

    def __repr__(self): # type: () -> str
        return 'TransitionDecl(%s, %s, %s, %s)' % (self.name, self.params,
                                                   self.mods, repr(self.expr))

    def __str__(self): # type: () -> str
        return 'transition %s(%s)\n  modifies %s\n  %s' % \
            (self.name,
             ', '.join([str(p) for p in self.params]),
             ', '.join([str(m) for m in self.mods]),
             self.expr)

    def to_z3(self, key, key_old): # type: (str, str) -> z3.ExprRef
        assert self.prog is not None

        bs = []
        for p in self.params:
            n = p.name
            assert p.sort is not None and not isinstance(p.sort, SortInferencePlaceholder)
            self.binders[n] = z3.Const(n, p.sort.to_z3())
            bs.append(self.binders[n])

        mods = []
        for d in self.prog.relations_and_constants():
            if not d.mutable or any(mc.decl == d for mc in self.mods):
                continue

            if isinstance(d, ConstantDecl) or len(d.arity) == 0:
                lhs = d.to_z3(key)
                rhs = d.to_z3(key_old)
                assert isinstance(lhs, z3.ExprRef) and isinstance(rhs, z3.ExprRef)
                e = lhs == rhs
            else:
                cs = [] # type: List[z3.ExprRef]
                i = 0
                for s in d.arity:
                    cs.append(z3.Const('x' + str(i), s.to_z3()))
                    i += 1

                lhs = d.to_z3(key)
                rhs = d.to_z3(key_old)
                assert isinstance(lhs, z3.FuncDeclRef) and isinstance(rhs, z3.FuncDeclRef)


                e = z3.Forall(cs, lhs(*cs) == rhs(*cs))


            mods.append(e)

        return z3.Exists(bs, z3.And(self.expr.to_z3(key, key_old), *mods))

class InvariantDecl(Decl):
    def __init__(self, tok, name, expr): # type: (Token, Optional[str], Expr) -> None
        self.tok = tok
        self.name = name
        self.expr = expr

    def resolve(self, scope): # type: (Scope) -> None
        self.expr = close_free_vars(self.expr)
        self.expr.resolve(scope, BoolSort)

    def __repr__(self): # type: () -> str
        return 'InvariantDecl(%s, %s)' % (self.name if self.name is not None else 'None',
                                          repr(self.expr))

    def __str__(self): # type: () -> str
        return 'invariant %s%s' % (('[%s] ' % self.name) if self.name is not None else '',
                                   self.expr)


class AxiomDecl(Decl):
    def __init__(self, tok, name, expr): # type: (Token, Optional[str], Expr) -> None
        self.tok = tok
        self.name = name
        self.expr = expr

    def resolve(self, scope): # type: (Scope) -> None
        self.expr.resolve(scope, BoolSort)

    def __repr__(self): # type: () -> str
        self.expr = close_free_vars(self.expr)
        return 'AxiomDecl(%s, %s)' % (self.name if self.name is not None else 'None',
                                      repr(self.expr))

    def __str__(self): # type: () -> str
        return 'axiom %s%s' % (('[%s] ' % self.name) if self.name is not None else '',
                               self.expr)


Binder = Union[RelationDecl, ConstantDecl, TransitionDecl, QuantifierExpr]

class Scope:
    def __init__(self, prog): # type: (Program) -> None
        self.stack = [] # type: List[Tuple[List[SortedVar], Binder]]
        self.sorts = {} # type: Dict[str, SortDecl]
        self.relations = {} # type: Dict[str, RelationDecl]
        self.constants = {} # type: Dict[str, ConstantDecl]
        self.prog = prog

    def push(self, vs, binder): # type: (List[SortedVar], Binder) -> None
        self.stack.append((vs, binder))

    def pop(self): # type: () -> None
        self.stack.pop()

    def get(self, name): # type: (str) -> Optional[Binder]
        # first, check for bound variables in scope
        for (vs, binder) in reversed(self.stack):
            for v in vs:
                if v.name == name:
                    return binder

        # otherwise, check for constants/relations (whose domains are disjoint)
        return self.constants.get(name) or self.relations.get(name)

    def add_constant(self, tok, constant, decl): # type: (Optional[Token], str, ConstantDecl) -> None
        assert len(self.stack) == 0

        if constant in self.constants:
            error(tok, 'Duplicate constant name %s' % (constant,))

        if constant in self.relations:
            error(tok, 'Constant name %s is already declared as a relation' %
                  (constant,))

        self.constants[constant] = decl

    def add_sort(self, tok, sort, decl): # type: (Optional[Token], str, SortDecl) -> None
        assert len(self.stack) == 0

        if sort in self.sorts:
            error(tok, 'Duplicate sort name %s' % (sort,))

        self.sorts[sort] = decl

    def get_sort(self, sort): # type: (str) -> Optional[SortDecl]
        return self.sorts.get(sort)

    def add_relation(self, tok, relation, decl): # type: (Optional[Token], str, RelationDecl) -> None
        assert len(self.stack) == 0

        if relation in self.relations:
            error(tok, 'Duplicate relation name %s' % (relation,))

        if relation in self.constants:
            error(tok, 'Relation name %s is already declared as a constant' % (relation,))

        self.relations[relation] = decl

    @contextmanager
    def in_scope(self, vs, binder): # type: (List[SortedVar], Binder) -> Iterator[None]
        n = len(self.stack)
        self.push(vs, binder)
        yield
        self.pop()
        assert n == len(self.stack)

class Program(object):
    def __init__(self, decls): # type: (List[Decl]) -> None
        self.decls = decls
        self.scope = None # type: Optional[Scope]

    def sorts(self): # type: () -> Iterator[SortDecl]
        for d in self.decls:
            if isinstance(d, SortDecl):
                yield d

    def inits(self): # type: () -> Iterator[InitDecl]
        for d in self.decls:
            if isinstance(d, InitDecl):
                yield d

    def invs(self): # type: () -> Iterator[InvariantDecl]
        for d in self.decls:
            if isinstance(d, InvariantDecl):
                yield d

    def transitions(self): # type: () -> Iterator[TransitionDecl]
        for d in self.decls:
            if isinstance(d, TransitionDecl):
                yield d

    def axioms(self): # type: () -> Iterator[AxiomDecl]
        for d in self.decls:
            if isinstance(d, AxiomDecl):
                yield d

    def relations_and_constants(self): # type: () -> Iterator[Union[RelationDecl, ConstantDecl]]
        for d in self.decls:
            if isinstance(d, RelationDecl) or \
               isinstance(d, ConstantDecl):
                yield d

    def decls_containing_exprs(self): # type: () -> Iterator[Union[InitDecl, TransitionDecl, InvariantDecl, AxiomDecl]]
        for d in self.decls:
            if isinstance(d, InitDecl) or \
               isinstance(d, TransitionDecl) or \
               isinstance(d, InvariantDecl) or \
               isinstance(d, AxiomDecl):
                yield d

    def resolve(self): # type: () -> None
        scope = Scope(self)
        self.scope = scope

        for s in self.sorts():
            s.resolve(scope)

        for rc in self.relations_and_constants():
            rc.resolve(scope)

        for d in self.decls_containing_exprs():
            d.resolve(scope)

        assert len(scope.stack) == 0

    def __repr__(self): # type: () -> str
        return 'Program(%s)' % (self.decls,)

    def __str__(self): # type: () -> str
        return '\n'.join(str(d) for d in self.decls)
            
