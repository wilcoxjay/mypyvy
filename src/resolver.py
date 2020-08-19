import syntax
from syntax import Expr, Bool, Int, UnaryExpr, BinaryExpr, NaryExpr, AppExpr, QuantifierExpr, Id, IfThenElse, Let

import copy

def resolve(scope: syntax.Scope, e: Expr) -> Expr:
    if isinstance(e, (Bool, Int)):
        return e
    elif isinstance(e, UnaryExpr):
        return UnaryExpr(e.op, resolve(scope, e.arg))
    elif isinstance(e, BinaryExpr):
        return BinaryExpr(e.op, resolve(scope, e.arg1), resolve(scope, e.arg2))
    elif isinstance(e, NaryExpr):
        return NaryExpr(e.op, tuple(resolve(scope, arg) for arg in e.args))
    elif isinstance(e, AppExpr):
        d = scope.get(e.callee)
        assert not isinstance(d, syntax.ConstantDecl) and not isinstance(d, tuple)
        return AppExpr(e.callee, tuple(resolve(scope, arg) for arg in e.args), resolved=d)
    elif isinstance(e, QuantifierExpr):
        
        with scope.in_scope(
    else:
        assert False
