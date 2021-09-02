
import re, itertools, random

from typing import Any, ContextManager, Dict, Protocol, Set, Tuple, cast
from dataclasses import dataclass, field
from enum import Enum
from semantics import FunctionInterp, RelationInterp, Trace, Universe
from syntax import AppExpr, BinaryExpr, ConstantDecl, Expr, FunctionDecl, Id, IfThenElse, Let, Bool, NaryExpr, New, Program, QuantifierExpr, RelationDecl, Sort, SortDecl, UnaryExpr, UninterpretedSort
import pycvc5

class SatResult(Enum):
    sat = 'sat'
    unsat = 'unsat'
    unknown = 'unknown'
    def __str__(self) -> str: return self.value

class SMTSolver(Protocol):
    def new_scope(self, n_states:int) -> ContextManager: ...
    def add_expr(self, e: Expr) -> None: ...
    def check(self) -> SatResult: ...
    def is_true(self, e: Expr) -> bool: ...
    def get_trace(self) -> Trace: ...

@dataclass
class _CVC5Context:
    solver: pycvc5.Solver
    sorts: Dict[str, pycvc5.Sort] = field(default_factory=dict)
    state_indices: Set[int] = field(default_factory=set)
    mutable_syms: Dict[Tuple[str, int], pycvc5.Term] = field(default_factory=dict)
    immutable_syms: Dict[str, pycvc5.Term] = field(default_factory=dict)

    def _sort_of(self, s: Sort) -> pycvc5.Sort:
        assert isinstance(s, UninterpretedSort)
        return self.sorts[s.name]
        
    def fill_from_prog(self, prog: Program) -> None:
        for sort in prog.sorts():
            self.sorts[sort.name] = self.solver.mkUninterpretedSort(sort.name)
        for rel in prog.relations():
            if not rel.mutable:
                args = [self._sort_of(s) for s in rel.arity]
                cvc5_sort = self.solver.mkFunctionSort(args, self.solver.getBooleanSort()) if len(args) > 0 else self.solver.getBooleanSort()
                self.immutable_syms[rel.name] = self.solver.mkConst(cvc5_sort, rel.name)
        
        for con in prog.constants():
            if not con.mutable:
                cvc5_sort = self._sort_of(con.sort)
                self.immutable_syms[con.name] = self.solver.mkConst(cvc5_sort, con.name)

        for fun in prog.functions():
            if not fun.mutable:
                args = [self._sort_of(s) for s in fun.arity]
                ret = self._sort_of(fun.sort)
                cvc5_sort = self.solver.mkFunctionSort(args, ret) if len(args) > 0 else ret
                self.immutable_syms[fun.name] = self.solver.mkConst(cvc5_sort, fun.name)

    def fill_state_from_prog(self, prog: Program, state_i: int) -> None:
        if state_i in self.state_indices: return
        self.state_indices.add(state_i)

        for rel in prog.relations():
            if rel.mutable:
                args = [self._sort_of(s) for s in rel.arity]
                cvc5_sort = self.solver.mkFunctionSort(args, self.solver.getBooleanSort()) if len(args) > 0 else self.solver.getBooleanSort()
                self.mutable_syms[(rel.name, state_i)] = self.solver.mkConst(cvc5_sort, f"__{state_i}_{rel.name}")

        for con in prog.constants():
            if con.mutable:
                cvc5_sort = self._sort_of(con.sort)
                self.mutable_syms[(con.name, state_i)] = self.solver.mkConst(cvc5_sort, con.name)

        for fun in prog.functions():
            if fun.mutable:
                args = [self._sort_of(s) for s in fun.arity]
                ret = self._sort_of(fun.sort)
                cvc5_sort = self.solver.mkFunctionSort(args, ret) if len(args) > 0 else ret
                self.mutable_syms[(fun.name, state_i)] = self.solver.mkConst(cvc5_sort, fun.name)
            
    def get_sym_term(self, sym: str, state_i: int = 0) -> pycvc5.Term:
        if sym in self.immutable_syms:
            return self.immutable_syms[sym]
        elif (sym, state_i) in self.mutable_syms:
            return self.mutable_syms[(sym, state_i)]
        else:
            print(f"Symbol {sym} not found")
            assert False

    def tr(self, e: Expr, state_i: int = 0, vars: Dict[str, pycvc5.Term] = {}) -> pycvc5.Term:
        if isinstance(e, Bool):
            return self.solver.mkBoolean(e.val)
        elif isinstance(e, UnaryExpr):
            if e.op == 'NEW':
                return self.tr(e.arg, state_i+1, vars)
            if e.op == 'NOT':
                return self.solver.mkTerm(pycvc5.kinds.Not, self.tr(e.arg, state_i, vars))
        elif isinstance(e, BinaryExpr):
            x = self.tr(e.arg1, state_i, vars)
            y = self.tr(e.arg2, state_i, vars)
            if e.op == 'IMPLIES':
                return self.solver.mkTerm(pycvc5.kinds.Implies, x, y)
            elif e.op == 'IFF':
                return self.solver.mkTerm(pycvc5.kinds.Equal, x, y)
            elif e.op == 'EQUAL':
                return self.solver.mkTerm(pycvc5.kinds.Equal, x, y)
            elif e.op == 'NOTEQ':
                return self.solver.mkTerm(pycvc5.kinds.Not, self.solver.mkTerm(pycvc5.kinds.Equal, x, y))
        elif isinstance(e, NaryExpr):
            if e.op == 'AND':
                return self.solver.mkTerm(pycvc5.kinds.And, *(self.tr(a, state_i, vars) for a in e.args))
            elif e.op == 'OR':
                return self.solver.mkTerm(pycvc5.kinds.Or, *(self.tr(a, state_i, vars) for a in e.args))
            elif e.op == 'DISTINCT':
                return self.solver.mkTerm(pycvc5.kinds.Distinct, *(self.tr(a, state_i, vars) for a in e.args))
        elif isinstance(e, AppExpr):
            callee = self.get_sym_term(e.callee, state_i)
            args = [self.tr(arg, state_i, vars) for arg in e.args]
            if len(args) > 0:
                return self.solver.mkTerm(pycvc5.kinds.ApplyUf, callee, *args)
            else:
                return callee # for func() with no args
        elif isinstance(e, Id):
            if e.name in vars:
                return vars[e.name]
            return self.get_sym_term(e.name, state_i)
        elif isinstance(e, QuantifierExpr):
            bvs = [(bv.name, self.solver.mkVar(self._sort_of(cast(Sort, bv.sort)), bv.name)) for bv in e.binder.vs]
            body = self.tr(e.body, state_i, {**vars, **{name: bv for name, bv in bvs}})
            q_kind = pycvc5.kinds.Exists if e.quant =='EXISTS' else pycvc5.kinds.Forall
            return self.solver.mkTerm(q_kind, self.solver.mkTerm(pycvc5.kinds.BoundVarList, *(v for (name, v) in bvs)), body)
        elif isinstance(e, IfThenElse):
            return self.solver.mkTerm(pycvc5.kinds.Ite, self.tr(e.branch, state_i, vars), self.tr(e.then, state_i, vars), self.tr(e.els, state_i, vars))
        elif isinstance(e, Let):
            pass
        else:
            assert False, (type(e), e)
        print(f"Couldn't translate: {e}")
        print(f"Type: {type(e)}")
        print(f"Repr: {repr(e)}")
        assert False, e

class CVC5Solver(SMTSolver):
    def __init__(self, program: Program, timeout: int = 0) -> None:
        self._program = program
        self._solver = pycvc5.Solver()
        self._solver.setOption("produce-models", "true")
        self._solver.setOption("fs-interleave", "true")
        self._solver.setOption("finite-model-find", "true")
        self._solver.setOption("seed", str(random.randint(0,10000000)))
        if timeout > 0:
            self._solver.setOption("tlimit-per", str(timeout))
        self._current_states = -1
        self._is_sat = False
        self._context = _CVC5Context(self._solver)

    @dataclass
    class ScopeContext:
        solver: 'CVC5Solver'
        n_states: int
        old_states: int = 0

        def __enter__(self) -> None:
            self.old_states = self.solver._current_states
            assert self.old_states < self.n_states
            self.solver._solver.push()
            self.solver._add_states(self.n_states)
        def __exit__(self, t: Any, value: Any, traceback: Any) -> None:
            self.solver._solver.pop()
            self.solver._current_states = self.old_states

    def new_scope(self, n_states: int) -> ScopeContext:
        return CVC5Solver.ScopeContext(self, n_states)

    def _add_states(self, new_states: int) -> None:
        assert new_states >= self._current_states
        for state_i in range(self._current_states, new_states):
            if state_i == -1:
                self._add_immutable()
            else:
                self._add_state_index(state_i)
            self._current_states = state_i
    
    def _add_immutable(self) -> None:
        self._context.fill_from_prog(self._program)
        for ax in self._program.axioms():
            self.add_expr(ax.expr)

    def _add_state_index(self, state_i: int) -> None:
        self._context.fill_state_from_prog(self._program, state_i)
        for dr in self._program.derived_relations():
            if dr.derived_axiom is not None:
                self.add_expr(New(dr.derived_axiom, state_i))

    def add_expr(self, e: Expr) -> None:
        # print("Adding", e)
        t = self._context.tr(e, 0, dict())
        # print("Became: ", t)
        self._solver.assertFormula(t)

    def check(self) -> SatResult:
        self._is_sat = False
        res = self._solver.checkSat()
        if res.isSat():
            self._is_sat = True
            return SatResult.sat
        elif res.isUnsat():
            return SatResult.unsat
        else:
            return SatResult.unknown
    def is_true(self, e: Expr) -> bool:
        return str(self._solver.getValue(self._context.tr(e, 0, dict()))) != 'false'
    def get_trace(self) -> Trace:
        assert self._is_sat
        N_states = self._current_states + 1
        trace = Trace(N_states)

        prog = self._program

        def sort_decl_of(sort: Sort) -> SortDecl:
            assert isinstance(sort, UninterpretedSort)
            d = prog.scope.sorts[sort.name]
            return d

        def name_of_term(t: pycvc5.Term) -> str:
            s = str(t)
            m = re.match('\(as (.+) [^ ]+\)', s)
            if m:
                return m.group(1)
            return s
        def get_univ(sort: str) -> Tuple[str, ...]:
            elems = self._solver.getDomainElements(self._context.sorts[sort])
            return tuple(name_of_term(e) for e in elems)

        for sort in self._context.sorts.keys():
            trace.univs[cast(SortDecl, prog.scope.get_sort(sort))] = get_univ(sort)

        def _extract_rel(rel: RelationDecl, state: int) -> RelationInterp:
            callee = self._context.get_sym_term(rel.name, state)
            args = [self._solver.getDomainElements(self._context.sorts[sort_decl_of(sort).name]) for sort in rel.arity]
            interp: Dict[Tuple[str, ...], bool] = {}
            if len(args) > 0:
                for t in itertools.product(*args):
                    interp[tuple(name_of_term(x) for x in t)] = str(self._solver.getValue(self._solver.mkTerm(pycvc5.kinds.ApplyUf, callee, *t))) == 'true'
            else:
                interp[()] = str(self._solver.getValue(callee)) == 'true'
            return interp

        def _extract_func(rel: FunctionDecl, state: int) -> FunctionInterp:
            callee = self._context.get_sym_term(rel.name, state)
            args = [self._solver.getDomainElements(self._context.sorts[sort_decl_of(sort).name]) for sort in rel.arity]
            interp: Dict[Tuple[str, ...], str] = {}
            if len(args) > 0:
                for t in itertools.product(*args):
                    interp[tuple(name_of_term(x) for x in t)] = name_of_term(self._solver.getValue(self._solver.mkTerm(pycvc5.kinds.ApplyUf, callee, *t)))
            else:
                interp[()] = name_of_term(self._solver.getValue(callee))
            return interp
        
        def _extract_const(rel: ConstantDecl, state: int) -> str:
            constant = self._context.get_sym_term(rel.name, state)
            return name_of_term(self._solver.getValue(constant))

        for rel in prog.relations():
            if rel.mutable:
                for i in range(N_states):
                    trace.rel_interps[i][rel] = _extract_rel(rel, i)
            else:
                trace.immut_rel_interps[rel] = _extract_rel(rel, 0)
        for func in prog.functions():
            if func.mutable:
                for i in range(N_states):
                    trace.func_interps[i][func] = _extract_func(func, i)
            else:
                trace.immut_func_interps[func] = _extract_func(func, 0)
        for const in prog.constants():
            if const.mutable:
                for i in range(N_states):
                    trace.const_interps[i][const] = _extract_const(const, i)
            else:
                trace.immut_const_interps[const] = _extract_const(const, 0)

        # print(trace)
        return trace

