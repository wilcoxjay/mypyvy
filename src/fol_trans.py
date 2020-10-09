
from syntax import *
from logic import *
from typing import Dict, List, Tuple, TypeVar, Iterable, FrozenSet, Union, Callable, Generator, Set, Optional, cast, Type, Collection

try:
    import separators  # type: ignore # TODO: remove this after we find a way for travis to have folseparators
    import separators.timer
    import separators.learn
except ModuleNotFoundError:
    raise NotImplementedError()

PDState = Tuple[Trace, int]

def eval_predicate(s: PDState, p: Expr) -> bool:
    r = s[0].as_state(s[1]).eval(p)
    assert isinstance(r, bool)
    return r

def prog_to_sig(prog: Program, two_state: bool = False) -> separators.logic.Signature:
    sig = separators.logic.Signature()
    def sort_to_name(s: Sort) -> str:
        assert isinstance(s, UninterpretedSort)
        return s.name
    for d in prog.decls:
        if isinstance(d, SortDecl):
            sig.sorts.add(d.name)
        elif isinstance(d, ConstantDecl):
            sig.constants[d.name] = sort_to_name(d.sort)
            if two_state and d.mutable:
                sig.constants[d.name+'\''] = sort_to_name(d.sort)
        elif isinstance(d, RelationDecl):
            sig.relations[d.name] = list(sort_to_name(s) for s in d.arity)
            if two_state and d.mutable:
                sig.relations[d.name+'\''] = list(sort_to_name(s) for s in d.arity)
        elif isinstance(d, FunctionDecl):
            sig.functions[d.name] = (list(sort_to_name(s) for s in d.arity), sort_to_name(d.sort))
            if two_state and d.mutable:
                sig.functions[d.name+'\''] = (list(sort_to_name(s) for s in d.arity), sort_to_name(d.sort))
    sig.finalize_sorts()
    return sig

def state_to_model(state: PDState) -> separators.logic.Model:
    return two_state_trace_to_model(state[0], two_state=False, old_index=state[1])
def two_state_trace_to_model(tr: Trace, two_state:bool = True, old_index:int = 0, new_index:int = 1) -> separators.logic.Model:
    sig = prog_to_sig(syntax.the_program, two_state=two_state)
    M = separators.logic.Model(sig)
    def constants(x: Dict[ConstantDecl, str], post_state:bool = False) -> None:
        for cd, e in x.items():
            res = M.add_constant(cd.name + ('\'' if post_state else ''), e)
            assert res
    def relations(x: Dict[RelationDecl, List[Tuple[List[str], bool]]], post_state:bool = False) -> None:
        for rd in x:
            for es, v in x[rd]:
                M.add_relation(rd.name + ('\'' if post_state else ''), es, True if v else False)
    def functions(x: Dict[FunctionDecl, List[Tuple[List[str], str]]], post_state:bool = False) -> None:
        for fd in x:
            for es, e in x[fd]:
                M.add_function(fd.name + ('\'' if post_state else ''), es, e)

    for sort in sorted(tr.univs.keys(), key=str):
        for e in tr.univs[sort]:
            M.add_elem(e, sort.name)

    constants(tr.immut_const_interps)
    constants(tr.const_interps[old_index])
    if two_state:
        constants(tr.const_interps[new_index], post_state=True)

    relations(tr.immut_rel_interps)
    relations(tr.rel_interps[old_index])
    if two_state:
        relations(tr.rel_interps[new_index], post_state=True)

    functions(tr.immut_func_interps)
    functions(tr.func_interps[old_index])
    if two_state:
        functions(tr.func_interps[new_index], post_state=True)

    return M

def predicate_to_formula(p: Expr, two_state:bool = False) -> separators.logic.Formula:
    L = separators.logic
    def q2f(b: Binder, is_forall: bool, f: L.Formula) -> L.Formula:
        for q in reversed(b.vs):
            assert isinstance(q.sort, UninterpretedSort)
            if is_forall:
                f = L.Forall(q.name, q.sort.name, f)
            else:
                f = L.Exists(q.name, q.sort.name, f)
        return f

    def p2f(p: Expr, old:bool) -> L.Formula:
        if isinstance(p, BinaryExpr):
            if p.op == 'EQUAL':
                return L.Equal(p2t(p.arg1, old), p2t(p.arg2, old))
            elif p.op == 'NOTEQ':
                return L.Not(L.Equal(p2t(p.arg1, old), p2t(p.arg2, old)))
            elif p.op == 'IMPLIES':
                return L.Implies(p2f(p.arg1, old), p2f(p.arg2, old))
            elif p.op == 'IFF':
                return L.Iff(p2f(p.arg1, old), p2f(p.arg2, old))
            else:
                assert False
        elif isinstance(p, NaryExpr):
            if p.op == 'AND':
                return L.And([p2f(a, old) for a in p.args])
            elif p.op == 'OR':
                return L.Or([p2f(a, old) for a in p.args])
            else:
                assert False
        elif isinstance(p, UnaryExpr):
            if p.op == 'NOT':
                return L.Not(p2f(p.arg, old))
            elif p.op == 'OLD':
                return p2f(p.arg, True)
            else:
                assert False
        elif isinstance(p, AppExpr):
            assert p.callee in [r.name for r in syntax.the_program.relations()] and "Definitions not supported"
            immutable = False
            for r in syntax.the_program.relations():
                if r.name == p.callee and not r.mutable:
                    immutable = True
            return L.Relation(p.callee if old or immutable else p.callee+'\'', [p2t(a, old) for a in p.args])
        elif isinstance(p, QuantifierExpr):
            return q2f(p.binder, p.quant == 'FORALL', p2f(p.body, old))                    
        elif isinstance(p, IfThenElse):
            return L.And([L.Implies(p2f(p.branch, old), p2f(p.then, old)), L.Implies(L.Not(p2f(p.branch, old)), p2f(p.els, old))])
        elif isinstance(p, Id):
            assert p.name in [r.name for r in syntax.the_program.relations()]
            immutable = False
            for r in syntax.the_program.relations():
                if r.name == p.name and not r.mutable:
                    immutable = True
            return L.Relation(p.name if old or immutable else p.name+'\'', [])
        elif isinstance(p, Bool):
            if p.val == True:
                return L.And([])
            else:
                return L.Or([])
        else:
            print("Failed", p, file = sys.stderr)
            assert False
    def p2t(p: Expr, old: bool) -> L.Term:
        if isinstance(p, Id):
            # in this case immutable is also true for quantified variables
            immutable = True
            for c in syntax.the_program.constants():
                if c.name == p.name and c.mutable:
                    immutable = False
            return L.Var(p.name if old or immutable else p.name+'\'')
        elif isinstance(p, AppExpr):
            #assert p.callee in self.sig.functions
            immutable = False
            for f in syntax.the_program.functions():
                if f.name == p.callee and not f.mutable:
                    immutable = True
            return L.Func(p.callee if old or immutable else p.callee+'\'', [p2t(a, old) for a in p.args])
        elif isinstance(p, UnaryExpr) and p.op == 'OLD':
            return p2t(p.arg, True)
        else:
            print(p)
            assert False
    f = p2f(p, not two_state)
    return f

def frame_to_formula(mods: Iterable[ModifiesClause]) -> separators.logic.Formula:
    L = separators.logic
    frame: List[separators.logic.Formula] = []
    for d in syntax.the_program.relations_constants_and_functions():
        if isinstance(d, ConstantDecl):
            if any(d.name == m.name for m in mods) or not d.mutable:
                continue
            frame.append(L.Equal(L.Var(d.name), L.Var(d.name+'\'')))
        elif isinstance(d, RelationDecl):
            if any(d.name == m.name for m in mods) or not d.mutable or d.is_derived():
                continue
            sorts = [cast(UninterpretedSort, s).name for s in d.arity]
            bvars = [f"__arg_{i}" for i in range(len(sorts))]
            r_a = L.Relation(d.name, [L.Var(v) for v in bvars])
            r_b = L.Relation(d.name+'\'', [L.Var(v) for v in bvars])
            body: L.Formula = L.Iff(r_a, r_b) 
            for bv,sort in zip(bvars, sorts):
                body = L.Forall(bv, sort, body)
            frame.append(body)
        elif isinstance(d, FunctionDecl):
            if any(d.name == m.name for m in mods) or not d.mutable:
                continue
            sorts = [cast(UninterpretedSort, s).name for s in d.arity]
            bvars = [f"__arg_{i}" for i in range(len(sorts))]
            f_a = L.Func(d.name, [L.Var(v) for v in bvars])
            f_b = L.Func(d.name+'\'', [L.Var(v) for v in bvars])
            body = L.Equal(f_a, f_b)
            for bv,sort in zip(bvars, sorts):
                body = L.Forall(bv, sort, body)
            frame.append(body)
        else:
            assert False
    return L.And(frame)

def transition_to_formula(trans: DefinitionDecl) -> separators.logic.Formula:
    L = separators.logic
    def q2f(b: Binder, is_forall: bool, f: L.Formula) -> L.Formula:
        for q in reversed(b.vs):
            assert isinstance(q.sort, UninterpretedSort)
            if is_forall:
                f = L.Forall(q.name, q.sort.name, f)
            else:
                f = L.Exists(q.name, q.sort.name, f)
        return f
    
    body = predicate_to_formula(trans.expr, two_state=True)
    frame = frame_to_formula(trans.mods)
    return L.And([q2f(trans.binder, False, body), frame])

def formula_to_predicate(f: separators.logic.Formula) -> Expr:
    def term_to_expr(t: separators.logic.Term) -> Expr:
        if isinstance(t, separators.logic.Var):
            return Id(None, t.var)
        elif isinstance(t, separators.logic.Func):
            return AppExpr(None, t.f, [term_to_expr(a) for a in t.args])
        else:
            assert False
    def formula_to_expr(f: separators.logic.Formula) -> Expr:
        if isinstance(f, separators.logic.And):
            return And(*(formula_to_expr(a) for a in f.c))
        elif isinstance(f, separators.logic.Or):
            return Or(*(formula_to_expr(a) for a in f.c))
        elif isinstance(f, separators.logic.Not):
            if isinstance(f.f, separators.logic.Equal): # special case !=
                return Neq(term_to_expr(f.f.args[0]), term_to_expr(f.f.args[1]))
            return Not(formula_to_expr(f.f))
        elif isinstance(f, separators.logic.Iff):
            return Iff(formula_to_expr(f.c[0]), formula_to_expr(f.c[1]))
        elif isinstance(f, separators.logic.Equal):
            return Eq(term_to_expr(f.args[0]), term_to_expr(f.args[1]))
        elif isinstance(f, separators.logic.Relation):
            if len(f.args) == 0:
                return Id(None, f.rel)
            else:
                return AppExpr(None, f.rel, [term_to_expr(a) for a in f.args])
        elif isinstance(f, separators.logic.Exists):
            body = formula_to_expr(f.f)
            v = SortedVar(None, f.var, UninterpretedSort(None, f.sort))
            if isinstance(body, QuantifierExpr) and body.quant == 'EXISTS':
                return Exists([v] + body.binder.vs, body.body)
            else:
                return Exists([v], body)
        elif isinstance(f, separators.logic.Forall):
            body = formula_to_expr(f.f)
            v = SortedVar(None, f.var, UninterpretedSort(None, f.sort))
            if isinstance(body, QuantifierExpr) and body.quant == 'FORALL':
                return Forall([v] + body.binder.vs, body.body)
            else:
                return Forall([v], body)
        else:
            assert False

    e = formula_to_expr(f)
    e.resolve(syntax.the_program.scope, BoolSort)
    return e

def model_to_state(m: separators.logic.Model) -> PDState:
    tr = Trace([KEY_ONE])
    prog = syntax.the_program
    for sort in prog.sorts():
        tr.univs[sort] = list(m.universe(sort.name))
    
    for cdecl in prog.constants():
        c = m.constants[cdecl.name]
        assert c is not None
        if cdecl.mutable:
            tr.const_interps[0][cdecl] = m.names[c]
        else:
            tr.immut_const_interps[cdecl] = m.names[c]
    
    for rdecl in prog.relations():
        for args, truth in m.relations[rdecl.name].items():
            if rdecl.mutable:
                tr.rel_interps[0].setdefault(rdecl,[]).append(([m.names[i] for i in args], truth))
            else:
                tr.immut_rel_interps.setdefault(rdecl,[]).append(([m.names[i] for i in args], truth))
    
    for fdecl in prog.functions():
        for args, val in m.functions[fdecl.name].items():
            if fdecl.mutable:
                tr.func_interps[0].setdefault(fdecl,[]).append(([m.names[i] for i in args], m.names[val]))
            else:
                tr.immut_func_interps.setdefault(fdecl,[]).append(([m.names[i] for i in args], m.names[val]))
    return (tr, 0)


class FOLSeparator(object):
    '''Class used to call into the folseparators code'''
    def __init__(self, states: List[PDState], sep: Optional[separators.separate.Separator] = None) -> None:
        prog = syntax.the_program
        self.states = states
        self.ids: Dict[int, int] = {}
        self.sig = prog_to_sig(prog, two_state=False)
        if sep is None:
            self.separator = separators.separate.HybridSeparator(self.sig, logic=utils.args.logic, quiet=True, expt_flags=utils.args.expt_flags)
        else:
            self.separator = sep

    def _state_id(self, i: int) -> int:
        assert 0 <= i < len(self.states)
        if i not in self.ids:
            # add a new state
            m = state_to_model(self.states[i])
            assert separators.logic.model_is_complete_wrt_sig(m, self.sig)
            self.ids[i] = self.separator.add_model(m)
        return self.ids[i]

    def separate(self,
                 pos: Collection[int],
                 neg: Collection[int],
                 imp: Collection[Tuple[int, int]],
                 complexity: int
    ) -> Optional[Expr]:
        mtimer = separators.timer.UnlimitedTimer()
        timer = separators.timer.UnlimitedTimer()
        with timer:
            f = self.separator.separate(
                pos=[self._state_id(i) for i in pos],
                neg=[self._state_id(i) for i in neg],
                imp=[(self._state_id(i), self._state_id(j)) for i, j in imp],
                max_depth=utils.args.max_depth,
                max_clauses=utils.args.max_clauses,
                max_complexity=complexity,
                timer=timer
            )
        if f is None:
            if False:
                _pos=[self._state_id(i) for i in pos]
                _neg=[self._state_id(i) for i in neg]
                _imp=[(self._state_id(i), self._state_id(j)) for i, j in imp]
                    
                fi = open("/tmp/error.fol", "w")
                fi.write(str(self.sig))
                for i,j in self.ids.items():
                    m = self.state_to_model(self.states[i])
                    m.label = str(j)
                    fi.write(str(m))
                fi.write(f"(constraint {' '.join(str(x) for x in _pos)})\n")
                fi.write(f"(constraint {' '.join('(not '+str(x)+')' for x in _neg)})\n")
                fi.write(f"(constraint {' '.join('(implies '+str(x)+' '+str(y)+')' for x, y in _imp)})\n")
            return None
        else:
            p = formula_to_predicate(f)
            for i in pos:
               assert eval_predicate(self.states[i], p)
            for i in neg:
               assert not eval_predicate(self.states[i], p)
            for i, j in imp:
               assert (not eval_predicate(self.states[i], p)) or eval_predicate(self.states[j], p)
            return p
