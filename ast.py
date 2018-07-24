import ply
import ply.lex
import ply.yacc

import z3
from typing import List, Union, Tuple, Optional, Dict, Iterator, Callable, Any
from contextlib import contextmanager

Token = ply.lex.LexToken

def error(tok, msg): # type: (Token, str) -> None
    raise Exception('%s: %s' % (tok.lineno, msg))

class Sort(object):
    def __repr__(self): # type: () -> str
        raise Exception('Unexpected sort does not implement __repr__ method')

    def resolve(self, scope): # type: (Scope) -> None
        raise Exception('Unexpected sort %s does not implement resolve method' % repr(self))

    def to_z3(self): # type: () -> z3.SortRef
        raise Exception('Unexpected sort %s does not implement to_z3 method' % repr(self))


class Expr(object):
    def __repr__(self): # type: () -> str
        raise Exception('Unexpected expr does not implement __repr__ method')

    def resolve(self, scope): # type: (Scope) -> None
        raise Exception('Unexpected expression %s does not implement resolve method' % repr(self))

    def to_z3(self, key=None, key_old=None, old=False):
        # type: (Optional[str], Optional[str], bool) -> z3.ExprRef
        raise Exception('Unexpected expression %s does not implement to_z3 method' % repr(self))

UNOPS = set([
    'NOT',
    'OLD'
])
z3_UNOPS = {
    'NOT': z3.Not,
    'OLD': None
} # type: Any
# Dict[str, Callable[[z3.ExprRef], z3.ExprRef]]


class UnaryExpr(Expr):
    def __init__(self, op, arg): # type: (str, Expr) -> None
        assert op in UNOPS
        self.op = op
        self.arg = arg
        self.z3 = {} # type: Dict[Optional[str], z3.ExprRef]

    def resolve(self, scope): # type: (Scope) -> None
        self.arg.resolve(scope)

    def __repr__(self): # type: () -> str
        return 'UnaryExpr(%s, %s)' % (self.op, repr(self.arg))

    def to_z3(self, key=None, key_old=None, old=False):
        # type: (Optional[str], Optional[str], bool) -> z3.ExprRef
        if key not in self.z3:
            if self.op == 'OLD':
                assert not old and key_old is not None
                self.z3[key] = self.arg.to_z3(key, key_old, True)
            else:
                self.z3[key] = z3_UNOPS[self.op](self.arg.to_z3(key, key_old, old))

        return self.z3[key]


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
    def __init__(self, op, arg1, arg2): # type: (str, Expr, Expr) -> None
        assert op in BINOPS
        self.op = op
        self.arg1 = arg1
        self.arg2 = arg2
        self.z3 = {} # type: Dict[Optional[str], z3.ExprRef]

    def resolve(self, scope): # type: (Scope) -> None
        self.arg1.resolve(scope)
        self.arg2.resolve(scope)

    def __repr__(self): # type: () -> str
        return 'BinaryExpr(%s, %s, %s)' % (self.op,
                                           repr(self.arg1),
                                           repr(self.arg2))

    def to_z3(self, key=None, key_old=None, old=False):
        # type: (Optional[str], Optional[str], bool) -> z3.ExprRef
        if key not in self.z3:
            self.z3[key] = z3_BINOPS[self.op](self.arg1.to_z3(key, key_old, old), self.arg2.to_z3(key, key_old, old))

        return self.z3[key]

class AppExpr(Expr):
    def __init__(self, rel, args): # type: (Token, List[Expr]) -> None
        self.rel = rel
        self.args = args
        self.decl = None # type: Optional[RelationDecl]
        self.z3 = {} # type: Dict[Optional[str], z3.ExprRef]

    def resolve(self, scope): # type: (Scope) -> None
        x = scope.get(self.rel)
        assert isinstance(x, RelationDecl)
        self.decl = x

        if self.decl is None:
            error(self.rel, 'Unresolved relation name %s' % self.rel.value)

        for arg in self.args:
            arg.resolve(scope)

    def __repr__(self): # type: () -> str
        return 'AppExpr(%s, %s)' % (self.rel.value, self.args)

    def to_z3(self, key=None, key_old=None, old=False):
        # type: (Optional[str], Optional[str], bool) -> z3.ExprRef
        assert self.decl is not None

        if key not in self.z3:
            if not old:
                k = key
            else:
                assert key_old is not None
                k = key_old
            R = self.decl.to_z3(k)
            assert isinstance(R, z3.FuncDeclRef)
            self.z3[key] = R(*(arg.to_z3(key, key_old, old) for arg in self.args))

        return self.z3[key]

class SortedVar(object):
    def __init__(self, name, sort): # type: (Token, Sort) -> None
        self.name = name
        self.sort = sort

    def resolve(self, scope): # type: (Scope) -> None
        self.sort.resolve(scope)

    def __repr__(self): # type: () -> str
        return 'SortedVar(%s, %s)' % (self.name.value, repr(self.sort))


QUANTS = set([
    'FORALL',
    'EXISTS'
])

class QuantifierExpr(Expr):
    def __init__(self, quant, vs, body): # type: (str, List[SortedVar], Expr) -> None
        assert quant in QUANTS
        self.quant = quant
        self.vs = vs
        self.body = body
        self.z3 = {} # type: Dict[Optional[str], z3.ExprRef]
        self.binders = {} # type: Dict[str, z3.ExprRef]

    def resolve(self, scope): # type: (Scope) -> None
        for sv in self.vs:
            sv.resolve(scope)

        with scope.in_scope(self.vs, self):
            self.body.resolve(scope)

    def __repr__(self): # type: () -> str
        return 'QuantifierExpr(%s, %s, %s)' % (self.quant, self.vs, repr(self.body))

    def to_z3(self, key=None, key_old=None, old=False):
        # type: (Optional[str], Optional[str], bool) -> z3.ExprRef
        if key not in self.z3:
            bs = []
            for sv in self.vs:
                n = sv.name.value
                self.binders[n] = z3.Const(n, sv.sort.to_z3())
                bs.append(self.binders[n])

            self.z3[key] = (z3.ForAll if self.quant == 'FORALL' else z3.Exists)(bs, self.body.to_z3(key, key_old, old))

        return self.z3[key]


class Id(Expr):
    '''Unresolved symbol (might represent a constant or a variable)'''
    def __init__(self, name): # type: (Token) -> None
        self.name = name
        self.decl = None # type: Optional[Binder]

    def resolve(self, scope): # type: (Scope) -> None
        self.decl = scope.get(self.name)
        if self.decl is None:
            error(self.name, 'Unresolved variable %s' % (self.name.value,))

    def __repr__(self): # type: () -> str
        return 'Id(%s, decl=%s)' % (self.name.value,
                                    id(self.decl) if self.decl is not None else 'None')

    def to_z3(self, key=None, key_old=None, old=False):
        # type: (Optional[str], Optional[str], bool) -> z3.ExprRef
        assert self.decl is not None

        if isinstance(self.decl, QuantifierExpr) or \
           isinstance(self.decl, TransitionDecl):
            return self.decl.binders[self.name.value]
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

Arity = List[Sort]

class UninterpretedSort(Sort):
    def __init__(self, name): # type: (Token) -> None
        self.name = name
        self.decl = None # type: Optional[SortDecl]

    def resolve(self, scope): # type: (Scope) -> None
        self.decl = scope.get_sort(self.name)
        if self.decl is None:
            error(self.name, 'Unresolved sort name %s' % (self.name.value,))

    def __repr__(self): # type: () -> str
        return 'UninterpretedSort(%s)' % (self.name.value,)

    def to_z3(self): # type: () -> z3.SortRef
        assert self.decl is not None

        return self.decl.to_z3()


# class BoolSort(Sort):
#     def resolve(self, scope):
#         pass


class Decl(object):
    def __repr__(self): # type: () -> str
        raise Exception('Unexpected decl does not implement __repr__ method')

class SortDecl(Decl):
    def __init__(self, name): # type: (Token) -> None
        self.name = name
        self.z3 = None # type: Optional[z3.SortRef]

    def resolve(self, scope): # type: (Scope) -> None
        scope.add_sort(self.name, self)

    def __repr__(self): # type: () -> str
        return 'SortDecl(%s)' % self.name.value

    def to_z3(self): # type: () -> z3.SortRef
        if self.z3 is None:
            self.z3 = z3.DeclareSort(self.name.value)

        return self.z3

class RelationDecl(Decl):
    def __init__(self, name, arity, mutable): # type: (Token, Arity, bool) -> None
        self.name = name
        self.arity = arity
        self.mutable = mutable
        self.mut_z3 = {} # type: Dict[str, Union[z3.FuncDeclRef, z3.ExprRef]]
        self.immut_z3 = None # type: Optional[Union[z3.FuncDeclRef, z3.ExprRef]]

    def resolve(self, scope): # type: (Scope) -> None
        for sort in self.arity:
            sort.resolve(scope)

        scope.add_relation(self.name, self)

    def __repr__(self): # type: () -> str
        return 'RelationDecl(%s, %s, mutable=%s)' % (self.name.value, self.arity, self.mutable)

    def to_z3(self, key): # type: (Optional[str]) -> Union[z3.FuncDeclRef, z3.ExprRef]
        if self.mutable:
            assert key is not None
            if key not in self.mut_z3:
                if len(self.arity) > 0:
                    a = [s.to_z3() for s in self.arity] + [z3.BoolSort()]
                    self.mut_z3[key] = z3.Function(key + '_' + self.name.value, *a)
                else:
                    self.mut_z3[key] = z3.Const(key + '_' + self.name.value, z3.BoolSort())

            return self.mut_z3[key]
        else:
            if self.immut_z3 is None:
                if len(self.arity) > 0:
                    a = [s.to_z3() for s in self.arity] + [z3.BoolSort()]
                    self.immut_z3 = z3.Function(self.name.value, *a)
                else:
                    self.immut_z3 = z3.Const(self.name.value, z3.BoolSort())

            return self.immut_z3


class ConstantDecl(Decl):
    def __init__(self, name, sort, mutable): # type: (Token, Sort, bool) -> None
        self.name = name
        self.sort = sort
        self.mutable = mutable
        self.mut_z3 = {} # type: Dict[str, z3.ExprRef]
        self.immut_z3 = None # type: Optional[z3.ExprRef]


    def __repr__(self): # type: () -> str
        return 'ConstantDecl(%s, %s, mutable=%s)' % (self.name.value, self.sort, self.mutable)

    def resolve(self, scope): # type: (Scope) -> None
        self.sort.resolve(scope)
        scope.add_constant(self.name, self)

    def to_z3(self, key): # type: (Optional[str]) -> z3.ExprRef
        if self.mutable:
            assert key is not None
            if key not in self.mut_z3:
                self.mut_z3[key] = z3.Const(key + '_' + self.name.value, self.sort.to_z3())

            return self.mut_z3[key]
        else:
            if self.immut_z3 is None:
                self.immut_z3 = z3.Const(self.name.value, self.sort.to_z3())

            return self.immut_z3


class InitDecl(Decl):
    def __init__(self, name, expr): # type: (Token, Expr) -> None
        self.name = name
        self.expr = expr

    def resolve(self, scope): # type: (Scope) -> None
        self.expr.resolve(scope)

    def __repr__(self): # type: () -> str
        return 'InitDecl(%s, %s)' % (self.name.value if self.name is not None else 'None',
                                     repr(self.expr))


class ModifiesClause(object):
    def __init__(self, name): # type: (Token) -> None
        self.name = name
        self.decl = None # type: Optional[Binder]

    def resolve(self, scope): # type: (Scope) -> None
        self.decl = scope.get(self.name)

        if self.decl is None:
            error(self.name, 'Unresolved constant or relation %s' % (self.name.value,))

    def __repr__(self): # type: () -> str
        return 'ModifiesClause(%s, %s)' % (self.name.value, repr(self.decl))


class TransitionDecl(Decl):
    def __init__(self, name, params, mods, expr):  # type: (Token, List[SortedVar], List[ModifiesClause], Expr) -> None
        self.name = name
        self.params = params
        self.mods = mods
        self.expr = expr
        self.prog = None # type: Optional[Program]
        self.z3 = {} # type: Dict[str, z3.ExprRef]
        self.binders = {} # type: Dict[str, z3.ExprRef]

    def resolve(self, scope): # type: (Scope) -> None
        assert len(scope.stack) == 0

        self.prog = scope.prog

        for param in self.params:
            param.resolve(scope)

        for mod in self.mods:
            mod.resolve(scope)

        with scope.in_scope(self.params, self):
            self.expr.resolve(scope)

    def __repr__(self): # type: () -> str
        return 'TransitionDecl(%s, %s, %s, %s)' % (self.name.value, self.params,
                                                   self.mods, repr(self.expr))

    def to_z3(self, key, key_old): # type: (str, str) -> z3.ExprRef
        assert self.prog is not None

        if key not in self.z3:
            bs = []
            for p in self.params:
                n = p.name.value
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

            self.z3[key] = z3.Exists(bs, z3.And(self.expr.to_z3(key, key_old), *mods))

        return self.z3[key]


class InvariantDecl(Decl):
    def __init__(self, name, expr): # type: (Token, Expr) -> None
        self.name = name
        self.expr = expr

    def resolve(self, scope): # type: (Scope) -> None
        self.expr.resolve(scope)

    def __repr__(self): # type: () -> str
        return 'InvariantDecl(%s, %s)' % (self.name.value if self.name is not None else 'None',
                                          repr(self.expr))


class AxiomDecl(Decl):
    def __init__(self, name, expr): # type: (Token, Expr) -> None
        self.name = name
        self.expr = expr

    def resolve(self, scope): # type: (Scope) -> None
        self.expr.resolve(scope)
        # TODO: check that no mutable relations are mentioned

    def __repr__(self): # type: () -> str
        return 'AxiomDecl(%s, %s)' % (self.name.value if self.name is not None else 'None',
                                      repr(self.expr))


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

    def get(self, name): # type: (Token) -> Optional[Binder]
        # first, check for bound variables in scope
        for (vs, binder) in reversed(self.stack):
            for v in vs:
                if v.name.value == name.value:
                    return binder

        # otherwise, check for constants/relations (whose domains are disjoint)
        return self.constants.get(name.value) or self.relations.get(name.value)

    def add_constant(self, constant, decl): # type: (Token, ConstantDecl) -> None
        assert len(self.stack) == 0

        if constant.value in self.constants:
            error(constant, 'Duplicate constant name %s' % (constant.value,))

        if constant.value in self.relations:
            error(constant, 'Constant name %s is already declared as a relation' %
                  (constant.value,))

        self.constants[constant.value] = decl

    def add_sort(self, sort, decl): # type: (Token, SortDecl) -> None
        if sort.value in self.sorts:
            error(sort, 'Duplicate sort name %s' % (sort.value,))

        self.sorts[sort.value] = decl

    def get_sort(self, sort): # type: (Token) -> Optional[SortDecl]
        return self.sorts.get(sort.value)

    def add_relation(self, relation, decl): # type: (Token, RelationDecl) -> None
        if relation.value in self.relations:
            error(relation, 'Duplicate relation name %s' % (relation.value,))

        if relation.value in self.constants:
            error(relation, 'Relation name %s is already declared as a constant' % (relation.value,))

        self.relations[relation.value] = decl

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

        for s in self.sorts():
            s.resolve(scope)

        for rc in self.relations_and_constants():
            rc.resolve(scope)

        for d in self.decls_containing_exprs():
            d.resolve(scope)


    def __repr__(self): # type: () -> str
        return 'Program(%s)' % (self.decls,)
            
