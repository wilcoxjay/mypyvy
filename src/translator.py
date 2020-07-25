from __future__ import annotations

import syntax
from syntax import Scope, Binder, Expr, Bool, Int, UnaryExpr, BinaryExpr, NaryExpr
from syntax import AppExpr, QuantifierExpr, Id, Let, IfThenElse, ModifiesClause
from syntax import DefinitionDecl, RelationDecl, FunctionDecl, ConstantDecl, StateDecl
from syntax import Program, SortDecl

from typing import Any, Callable, cast, Dict, Iterable, Iterator, List, Optional, Tuple

import itertools
import z3
import z3_utils
from networkx import DiGraph  # type: ignore

z3_UNOPS: Dict[str, Optional[Callable[[z3.ExprRef], z3.ExprRef]]] = {
    'NOT': z3.Not,
    'NEW': None
}

z3_BINOPS: Dict[str, Callable[[z3.ExprRef, z3.ExprRef], z3.ExprRef]] = {
    'IMPLIES': z3.Implies,
    'IFF': lambda x, y: x == y,
    'EQUAL': lambda x, y: x == y,
    'NOTEQ': lambda x, y: x != y,
    'GE': lambda x, y: x >= y,
    'GT': lambda x, y: x > y,
    'LE': lambda x, y: x <= y,
    'LT': lambda x, y: x < y,
    'PLUS': lambda x, y: x + y,
    'SUB': lambda x, y: x - y,
}

z3_NOPS: Any = {
    'AND': z3.And,
    'OR': z3.Or,
    'DISTINCT': z3.Distinct,
}


class Z3Translator(object):
    def __init__(self, scope: Scope[z3.ExprRef], keys: Tuple[str, ...] = ()) -> None:
        self.scope = scope
        self.keys = keys
        self.counter = 0

    def bind(self, binder: Binder) -> List[z3.ExprRef]:
        bs = []
        for sv in binder.vs:
            # in the presence of shadowing, we need to make sure every call to z3.Const is for a unique name
            n = sv.name + '_%s' % (self.counter,)
            self.counter += 1
            assert sv.sort is not None and not isinstance(sv.sort, syntax.SortInferencePlaceholder)
            bs.append(z3.Const(n, sv.sort.to_z3()))
        return bs

    def get_key_opt(self, index: int) -> Optional[str]:
        if index < len(self.keys):
            return self.keys[index]
        else:
            return None

    def translate_expr(self, expr: Expr, index: int = 0) -> z3.ExprRef:
        if isinstance(expr, Bool):
            return z3.BoolVal(expr.val)
        elif isinstance(expr, Int):
            return z3.IntVal(expr.val)
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
                # checked by resolver; see NOTE(calling-stateful-definitions)
                assert index + d.num_states <= len(self.keys)
                # now translate args in the scope of caller
                translated_args = [self.translate_expr(arg, index) for arg in expr.args]
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
            assert d is not None, expr.name
            if isinstance(d, RelationDecl) or \
               isinstance(d, ConstantDecl) or \
               isinstance(d, FunctionDecl):
                k = self.get_key_opt(index)
                assert not d.mutable or k is not None
                x = d.to_z3(k)
                assert isinstance(x, z3.ExprRef)
                return x
            elif isinstance(d, DefinitionDecl):
                # checked in resolver; see NOTE(calling-stateful-definitions)
                assert index + d.num_states <= len(self.keys)
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
            if not d.mutable or (isinstance(d, RelationDecl) and d.is_derived()) or \
               any(mc.name == d.name for mc in mods):
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

    def translate_transition_body(self, t: DefinitionDecl, index: int = 0) -> z3.ExprRef:
        return z3.And(self.translate_expr(t.expr, index=index),
                      *self.frame(t.mods, index=index))

    def translate_transition(self, t: DefinitionDecl, index: int = 0) -> z3.ExprRef:
        bs = self.bind(t.binder)
        with self.scope.in_scope(t.binder, bs):
            body = self.translate_transition_body(t, index=index)
            if bs:
                return z3.Exists(bs, body)
            else:
                return body

def sort_from_z3sort(prog: Program, z3sort: z3.SortRef) -> SortDecl:
    return prog.scope.get_sort_checked(str(z3sort))

def qa_edges_expr(prog: Program, expr: Expr) -> Iterator[Tuple[str, str]]:
    lator = Z3Translator(cast(Scope[z3.ExprRef], prog.scope))
    z3expr = lator.translate_expr(expr)
    for (ssortz3, tsortz3) in z3_utils.z3_quantifier_alternations(z3expr):
        yield (sort_from_z3sort(prog, ssortz3).name,
               sort_from_z3sort(prog, tsortz3).name)  # TODO: consider overriding equals instead of using the names


def quantifier_alternation_graph(prog: Program, exprs: List[Expr]) -> DiGraph:
    qa_graph = DiGraph()

    for expr in exprs:
        qa_graph.add_edges_from(qa_edges_expr(prog, expr))

    return qa_graph

def decls_quantifier_alternation_graph(prog: Program, additional: List[Expr]) -> DiGraph:
    res = quantifier_alternation_graph(prog,
                                       [axiom.expr for axiom in prog.axioms()] +
                                       [cast(Expr, rel.derived_axiom) for rel in prog.derived_relations()] +
                                       additional)
    for f in prog.functions():
        for asort in f.arity:
            esort = f.sort
            res.add_edge(prog.scope.get_sort_checked(str(asort)).name,
                         prog.scope.get_sort_checked(str(esort)).name)

    return res
