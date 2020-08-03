from __future__ import annotations

from itertools import chain, product

from typing import Any, Callable, cast, Dict, Iterable, Iterator, List, Optional, Tuple, Union

import z3
from networkx import DiGraph  # type: ignore

import syntax
from syntax import Scope, Binder, Expr, Bool, Int, UnaryExpr, BinaryExpr, NaryExpr
from syntax import AppExpr, QuantifierExpr, Id, Let, IfThenElse, ModifiesClause
from syntax import DefinitionDecl, RelationDecl, FunctionDecl, ConstantDecl, StateDecl
from syntax import Program, SortDecl, New
from semantics import Trace, Element, RelationInterp, FunctionInterp, RelationInterps, FunctionInterps
from z3_utils import z3_quantifier_alternations


TRANSITION_INDICATOR = 'tid'


class Z3Translator:
    z3_UNOPS: Dict[str, Callable[[z3.ExprRef], z3.ExprRef]] = {
        'NOT': z3.Not,
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
        'MULT': lambda x, y: x * y,
    }

    z3_NOPS: Dict[str, Callable[[List[z3.ExprRef]], z3.ExprRef]] = {
        'AND': cast(Callable[[List[z3.ExprRef]], z3.ExprRef], z3.And),
        'OR': cast(Callable[[List[z3.ExprRef]], z3.ExprRef], z3.Or),
        'DISTINCT': cast(Callable[[List[z3.ExprRef]], z3.ExprRef], z3.Distinct),
    }

    z3_QUANT: Dict[str, Callable[[List[z3.ExprRef], z3.ExprRef], z3.ExprRef]] = {
        'FORALL': z3.ForAll,
        'EXISTS': z3.Exists,
    }

    def __init__(self, scope: Scope[z3.ExprRef], num_states: int) -> None:
        assert num_states >= 0
        self.num_states = num_states
        self.scope = scope
        self.counter = 0

    @staticmethod
    def _get_keys(num_states: int) -> Tuple[str, ...]:
        # TODO: eliminate this
        return tuple(f'_{i}_' for i in range(num_states))

    def get_key(self, i: int) -> str:
        '''
        Return key for state i, i.e., i applications of new()
        '''
        # TODO: maybe have special key for immutables and for indicator variables
        assert 0 <= i < self.num_states
        return f'_{i}_'

    def bind(self, binder: Binder) -> List[z3.ExprRef]:
        bs = []
        for sv in binder.vs:
            # in the presence of shadowing, we need to make sure every call to z3.Const is for a unique name
            # ODED: it seems that after definitions are refactored out of Z3Translator, we could just use sv.name
            #       as the Z3 name, without adding a counter, and let Z3 handle the shadowing
            n = f'{sv.name}_{self.counter}'
            self.counter += 1
            assert sv.sort is not None and not isinstance(sv.sort, syntax.SortInferencePlaceholder)
            bs.append(z3.Const(n, Z3Translator.sort_to_z3(sv.sort)))
        return bs

    def translate_expr(self, expr: Expr) -> z3.ExprRef:
        assert self.scope.num_states == 0, self.scope.num_states
        assert self.scope.current_state_index == 0, self.scope.current_state_index
        with self.scope.n_states(self.num_states):
            return self.__translate_expr(expr)

    def _decl_to_z3(self, d: syntax.StateDecl) -> Union[z3.FuncDeclRef, z3.ExprRef]:
        return Z3Translator.statedecl_to_z3(
            d,
            self.get_key(self.scope.current_state_index)
            if d.mutable else None
        )

    def __translate_expr(self, expr: Expr) -> z3.ExprRef:
        if isinstance(expr, Bool):
            return z3.BoolVal(expr.val)
        elif isinstance(expr, Int):
            return z3.IntVal(expr.val)
        elif isinstance(expr, UnaryExpr) and expr.op in self.z3_UNOPS:
            return self.z3_UNOPS[expr.op](self.__translate_expr(expr.arg))
        elif isinstance(expr, UnaryExpr) and expr.op == 'NEW':
            assert self.scope.new_allowed()
            with self.scope.next_state_index():
                return self.__translate_expr(expr.arg)
        elif isinstance(expr, BinaryExpr) and expr.op in self.z3_BINOPS:
            return self.z3_BINOPS[expr.op](
                self.__translate_expr(expr.arg1),
                self.__translate_expr(expr.arg2)
            )
        elif isinstance(expr, NaryExpr) and expr.op in self.z3_NOPS:
            return self.z3_NOPS[expr.op]([self.__translate_expr(arg) for arg in expr.args])
        elif isinstance(expr, AppExpr):
            d = self.scope.get(expr.callee)
            if isinstance(d, DefinitionDecl):
                # TODO: handling definitions should be refactored out of Z3Translator
                # checked by typechecker; see NOTE(calling-stateful-definitions)
                assert self.scope.current_state_index + d.num_states <= self.scope.num_states, f'{d}\n{expr}'
                # now translate args in the scope of caller
                translated_args = [self.__translate_expr(arg) for arg in expr.args]
                with self.scope.fresh_stack():
                    with self.scope.in_scope(d.binder, translated_args):
                        return self.__translate_expr(d.expr)  # translate body of def in fresh scope
            elif isinstance(d, (RelationDecl, FunctionDecl)):
                callee = self._decl_to_z3(d)
                assert isinstance(callee, z3.FuncDeclRef), f'{callee}\n{expr}'
                return callee(*(
                    self.__translate_expr(arg)
                    for arg in expr.args
                ))
            else:
                assert False, f'{d}\n{expr}'
        elif isinstance(expr, QuantifierExpr) and expr.quant in self.z3_QUANT:
            bs = self.bind(expr.binder)
            with self.scope.in_scope(expr.binder, bs):
                e = self.__translate_expr(expr.body)
            return self.z3_QUANT[expr.quant](bs, e)
        elif isinstance(expr, Id):
            d = self.scope.get(expr.name)
            assert d is not None, f'{expr.name}\n{expr}'
            if isinstance(d, (RelationDecl, ConstantDecl)):
                z3sym = self._decl_to_z3(d)
                assert isinstance(z3sym, z3.ExprRef)
                return z3sym
            elif isinstance(d, DefinitionDecl):
                # TODO: handling definitions should be refactored out of Z3Translator
                # checked in typechecker; see NOTE(calling-stateful-definitions)
                assert self.scope.current_state_index + d.num_states <= self.scope.num_states
                with self.scope.fresh_stack():
                    return self.__translate_expr(d.expr)
            else:
                assert not isinstance(d, FunctionDecl)  # impossible since functions have arity > 0
                e, = d
                return e
        elif isinstance(expr, IfThenElse):
            return z3.If(self.__translate_expr(expr.branch),
                         self.__translate_expr(expr.then),
                         self.__translate_expr(expr.els))
        elif isinstance(expr, Let):
            val = self.__translate_expr(expr.val)
            with self.scope.in_scope(expr.binder, [val]):
                return self.__translate_expr(expr.body)
        else:
            assert False, expr

    @staticmethod
    def model_to_trace(z3model: z3.ModelRef, num_states: int, allow_undefined: bool = False) -> Trace:
        '''
        Convert z3 model to Trace with given number of states.

        If allow_undefined is True, the resulting trace may leave some symbols undefined.
        '''
        trace = Trace(num_states)
        keys = Z3Translator._get_keys(num_states)

        def rename(s: str) -> str:
            return s.replace('!val!', '').replace('@uc_', '')

        def _eval(expr: z3.ExprRef) -> z3.ExprRef:
            ans = z3model.eval(expr, model_completion=True)
            assert bool(ans) is True or bool(ans) is False, (expr, ans)
            return ans

        prog = syntax.the_program

        for z3sort in sorted(z3model.sorts(), key=str):
            sort = prog.scope.get_sort(str(z3sort))
            assert sort is not None
            univ = z3model.get_universe(z3sort)
            trace.univs[sort] = tuple(sorted(rename(str(x)) for x in univ))

        model_decls = z3model.decls()
        all_decls = model_decls
        for z3decl in sorted(all_decls, key=str):
            z3name = str(z3decl)
            for i, k in enumerate(keys):
                if z3name.startswith(k):
                    name = z3name[len(k + '_'):]
                    R = trace.rel_interps[i]
                    C = trace.const_interps[i]
                    F = trace.func_interps[i]
                    break
            else:
                name = z3name
                R = trace.immut_rel_interps
                C = trace.immut_const_interps
                F = trace.immut_func_interps

            decl = prog.scope.get(name)
            assert not isinstance(decl, syntax.Sort) and \
                not isinstance(decl, syntax.SortInferencePlaceholder)
            if decl is not None:
                if isinstance(decl, RelationDecl):
                    if decl.arity:
                        rl: RelationInterp = {}
                        domains = [z3model.get_universe(z3decl.domain(i))
                                   for i in range(z3decl.arity())]
                        if not any(x is None for x in domains):
                            # Note: if any domain is None, we silently drop this symbol.
                            # It's not entirely clear that this is an ok thing to do.
                            g = product(*domains)
                            for row in g:
                                relation_expr = z3decl(*row)
                                ans = _eval(relation_expr)
                                rl[tuple(rename(str(col)) for col in row)] = bool(ans)
                            assert decl not in R
                            R[decl] = rl
                    else:
                        ans = z3model.eval(z3decl())
                        assert decl not in R
                        R[decl] = {(): bool(ans)}
                elif isinstance(decl, FunctionDecl):
                    fl: FunctionInterp  = {}
                    domains = [z3model.get_universe(z3decl.domain(i))
                               for i in range(z3decl.arity())]
                    if not any(x is None for x in domains):
                        # Note: if any domain is None, we silently drop this symbol.
                        # It's not entirely clear that this is an ok thing to do.
                        g = product(*domains)
                        for row in g:
                            ans = z3model.eval(z3decl(*row))
                            if z3.is_int_value(ans):
                                ans_str = str(ans.as_long())
                            else:
                                ans_str = rename(ans.decl().name())

                            fl[tuple(rename(str(col)) for col in row)]= ans_str
                        assert decl not in F
                        F[decl] = fl
                else:
                    assert isinstance(decl, ConstantDecl)
                    v = z3model.eval(z3decl())
                    if z3.is_int_value(v):
                        v_str = str(v.as_long())
                    else:
                        v_str = rename(v.decl().name())

                    assert decl not in C
                    C[decl] = v_str
            else:
                if name.startswith(TRANSITION_INDICATOR + '_') and z3model.eval(z3decl()):
                    name = name[len(TRANSITION_INDICATOR + '_'):]
                    istr, name = name.split('_', maxsplit=1)
                    i = int(istr)
                    if i < len(trace.transitions):
                        trace.transitions[i] = name
                    else:
                        # TODO: not sure what's going on here with check_bmc and pd.check_k_state_implication
                        # assert False
                        pass

        if allow_undefined:
            return trace

        def get_univ(d: SortDecl) -> Tuple[Element, ...]:
            if d not in trace.univs:
                trace.univs[d] = (d.name + '0',)
            return trace.univs[d]

        def arbitrary_interp_r(r: RelationDecl) -> RelationInterp:
            doms = [get_univ(syntax.get_decl_from_sort(s)) for s in r.arity]
            return dict.fromkeys(product(*doms), False)

        def ensure_defined_r(r: RelationDecl) -> None:
            arb_interp: Optional[RelationInterp] = None
            for m in (trace.rel_interps if r.mutable else [trace.immut_rel_interps]):
                if r not in m:
                    if arb_interp is None:
                        arb_interp = arbitrary_interp_r(r)
                    m[r] = arb_interp

        def arbitrary_interp_c(c: ConstantDecl) -> Element:
            if isinstance(c.sort, syntax._BoolSort):
                return 'false'
            elif isinstance(c.sort, syntax._IntSort):
                return '0'
            assert isinstance(c.sort, syntax.UninterpretedSort)
            sort = c.sort
            return get_univ(syntax.get_decl_from_sort(sort))[0]

        def ensure_defined_c(c: ConstantDecl) -> None:
            arb_interp = arbitrary_interp_c(c)
            for m in (trace.const_interps if c.mutable else [trace.immut_const_interps]):
                if c not in m:
                    m[c] = arb_interp

        def arbitrary_interp_f(f: FunctionDecl) -> FunctionInterp:
            doms = [get_univ(syntax.get_decl_from_sort(s)) for s in f.arity]
            image = get_univ(syntax.get_decl_from_sort(f.sort))[0]
            return dict.fromkeys(product(*doms), image)

        def ensure_defined_f(f: FunctionDecl) -> None:
            arb_interp: Optional[FunctionInterp] = None
            for m in (trace.func_interps if f.mutable else [trace.immut_func_interps]):
                if f not in m:
                    if arb_interp is None:
                        arb_interp = arbitrary_interp_f(f)
                    m[f] = arb_interp

        for decl in prog.relations_constants_and_functions():
            if isinstance(decl, RelationDecl):
                ensure_defined_r(decl)
            elif isinstance(decl, ConstantDecl):
                ensure_defined_c(decl)
            elif isinstance(decl, FunctionDecl):
                ensure_defined_f(decl)
            else:
                assert False, decl

        return trace

    @staticmethod
    def sort_to_z3(s: Union[syntax.Sort, syntax.SortDecl]) -> z3.SortRef:
        if isinstance(s, syntax.UninterpretedSort):
            assert s.decl is not None, str(s)
            s = s.decl

        if isinstance(s, syntax.SortDecl):
            if s.z3 is None:
                s.z3 = z3.DeclareSort(s.name)
            return s.z3
        elif isinstance(s, syntax._BoolSort):
            return z3.BoolSort()
        elif isinstance(s, syntax._IntSort):
            return z3.IntSort()
        else:
            assert False

    @staticmethod
    def function_to_z3(f: syntax.FunctionDecl, key: Optional[str]) -> z3.FuncDeclRef:
        if f.mutable:
            assert key is not None
            if key not in f.mut_z3:
                a = [Z3Translator.sort_to_z3(s) for s in f.arity] + [Z3Translator.sort_to_z3(f.sort)]
                f.mut_z3[key] = z3.Function(key + '_' + f.name, *a)

            return f.mut_z3[key]
        else:
            if f.immut_z3 is None:
                a = [Z3Translator.sort_to_z3(s) for s in f.arity] + [Z3Translator.sort_to_z3(f.sort)]
                f.immut_z3 = z3.Function(f.name, *a)

            return f.immut_z3

    @staticmethod
    def relation_to_z3(r: syntax.RelationDecl, key: Optional[str]) -> Union[z3.FuncDeclRef, z3.ExprRef]:
        if r.mutable:
            assert key is not None
            if key not in r.mut_z3:
                if r.arity:
                    a = [Z3Translator.sort_to_z3(s) for s in r.arity] + [z3.BoolSort()]
                    r.mut_z3[key] = z3.Function(key + '_' + r.name, *a)
                else:
                    r.mut_z3[key] = z3.Const(key + '_' + r.name, z3.BoolSort())

            return r.mut_z3[key]
        else:
            if r.immut_z3 is None:
                if r.arity:
                    a = [Z3Translator.sort_to_z3(s) for s in r.arity] + [z3.BoolSort()]
                    r.immut_z3 = z3.Function(r.name, *a)
                else:
                    r.immut_z3 = z3.Const(r.name, z3.BoolSort())

            return r.immut_z3

    @staticmethod
    def constant_to_z3(c: syntax.ConstantDecl, key: Optional[str]) -> z3.ExprRef:
        if c.mutable:
            assert key is not None
            if key not in c.mut_z3:
                c.mut_z3[key] = z3.Const(key + '_' + c.name, Z3Translator.sort_to_z3(c.sort))

            return c.mut_z3[key]
        else:
            if c.immut_z3 is None:
                c.immut_z3 = z3.Const(c.name, Z3Translator.sort_to_z3(c.sort))

            return c.immut_z3

    @staticmethod
    def statedecl_to_z3(d: syntax.StateDecl, key: Optional[str]) -> Union[z3.FuncDeclRef, z3.ExprRef]:
        if isinstance(d, syntax.RelationDecl):
            return Z3Translator.relation_to_z3(d, key)
        elif isinstance(d, syntax.ConstantDecl):
            return Z3Translator.constant_to_z3(d, key)
        elif isinstance(d, syntax.FunctionDecl):
            return Z3Translator.function_to_z3(d, key)
        else:
            assert False, d

    @staticmethod
    def sort_from_z3sort(prog: Program, z3sort: z3.SortRef) -> SortDecl:
        return prog.scope.get_sort_checked(str(z3sort))


# ODED: I think the functions below should be implemented in logic.py or elsewhere, independent of z3


def qa_edges_expr(prog: Program, expr: Expr) -> Iterator[Tuple[str, str]]:
    lator = Z3Translator(cast(Scope[z3.ExprRef], prog.scope), 0)
    z3expr = lator.translate_expr(expr)
    for (ssortz3, tsortz3) in z3_quantifier_alternations(z3expr):
        # TODO: consider overriding equals instead of using the names
        yield (Z3Translator.sort_from_z3sort(prog, ssortz3).name,
               Z3Translator.sort_from_z3sort(prog, tsortz3).name)


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
