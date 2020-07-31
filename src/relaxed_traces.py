import logic
from logic import Trace, Diagram, Solver
import resolver
import syntax
from syntax import Expr
from trace import bmc_trace
import translator
from updr import RelaxedTrace
import utils
from utils import Set

import copy
import z3
import itertools
import networkx  # type: ignore
from typing import List, Callable, Union, Dict, TypeVar, Tuple, Optional, cast, Mapping, Sequence, Iterable

T = TypeVar('T')

def relaxed_program(prog: syntax.Program) -> syntax.Program:
    new_decls: List[syntax.Decl] = [d for d in prog.sorts()]

    actives: Dict[syntax.SortDecl, syntax.RelationDecl] = {}
    for sort in prog.sorts():
        name = prog.scope.fresh('active_' + sort.name)
        r = syntax.RelationDecl(name, arity=[syntax.UninterpretedSort(sort.name)],
                                mutable=True, derived=None, annotations=[])
        actives[sort] = r
        new_decls.append(r)

    # active relations initial conditions: always true
    for sort in prog.sorts():
        name = prog.scope.fresh(sort.name[0].upper())
        expr = syntax.Forall([syntax.SortedVar(name, None)],
                             syntax.Apply(actives[sort].name, [syntax.Id(name)]))
        new_decls.append(syntax.InitDecl(name=None, expr=expr))

    for d in prog.decls:
        if isinstance(d, syntax.SortDecl):
            pass  # already included above
        elif isinstance(d, syntax.RelationDecl):
            if d.derived_axiom is not None:
                expr = syntax.relativize_quantifiers(actives, d.derived_axiom)
                new_decls.append(syntax.RelationDecl(d.name, d.arity, d.mutable, expr,
                                                     d.annotations))
            else:
                new_decls.append(d)
        elif isinstance(d, syntax.ConstantDecl):
            new_decls.append(d)
        elif isinstance(d, syntax.FunctionDecl):
            new_decls.append(d)
        elif isinstance(d, syntax.AxiomDecl):
            new_decls.append(d)
        elif isinstance(d, syntax.InitDecl):
            new_decls.append(d)
        elif isinstance(d, syntax.DefinitionDecl):
            relativized_def = relativize_decl(d, actives, prog.scope, inline_relax_actives=False)
            new_decls.append(relativized_def)
        elif isinstance(d, syntax.InvariantDecl):
            expr = syntax.relativize_quantifiers(actives, d.expr)
            new_decls.append(syntax.InvariantDecl(d.name, expr=expr,
                                                  is_safety=d.is_safety, is_sketch=d.is_sketch))
        else:
            assert False, d

    new_decls.append(relaxation_action_def(prog, actives=actives, fresh=True))

    res = syntax.Program(new_decls)
    resolver.resolve_program(res)  # #sorrynotsorry
    return res


def relativize_decl(d: syntax.DefinitionDecl, actives: Dict[syntax.SortDecl, syntax.RelationDecl],
                    scope: syntax.Scope, inline_relax_actives: bool) -> syntax.DefinitionDecl:
    mods, expr = d.mods, d.expr
    expr = syntax.relativize_quantifiers(actives, expr)
    if d.is_public_transition:
        guard = syntax.relativization_guard_for_binder(actives, d.binder)
        expr = syntax.And(guard, expr)

    if inline_relax_actives:
        new_mods, new_conjs = relax_actives_action_chunk(scope, actives)
        mods += new_mods
        expr = syntax.And(expr, *new_conjs)

    relativized_def = syntax.DefinitionDecl(d.is_public_transition, d.num_states, d.name,
                                            params=d.binder.vs, mods=mods, expr=expr)
    return relativized_def


def relaxation_action_def(
        prog: syntax.Program,
        actives: Optional[Dict[syntax.SortDecl, syntax.RelationDecl]] = None,
        fresh: bool = True
) -> syntax.DefinitionDecl:
    decrease_name = (prog.scope.fresh('decrease_domain') if fresh else 'decrease_domain')
    mods = []
    conjs: List[Expr] = []
    if actives is None:
        actives = active_rel_by_sort(prog)

    # a conjunct allowing each domain to decrease
    new_mods, new_conjs = relax_actives_action_chunk(prog.scope, actives)
    mods += new_mods
    conjs += new_conjs

    # constants are active
    for const in prog.constants():
        conjs.append(syntax.New(syntax.Apply(actives[syntax.get_decl_from_sort(const.sort)].name,
                                             [syntax.Id(const.name)])))

    # functions map active to active
    for func in prog.functions():
        names: List[str] = []
        func_conjs = []
        for arg_sort in func.arity:
            arg_sort_decl = syntax.get_decl_from_sort(arg_sort)
            name = prog.scope.fresh(arg_sort_decl.name[0].upper(),
                                    also_avoid=names)
            names.append(name)
            func_conjs.append(syntax.New(syntax.Apply(actives[arg_sort_decl].name, [syntax.Id(name)])))
        ap_func = syntax.Apply(func.name, [syntax.Id(name) for name in names])
        name = prog.scope.fresh('y', also_avoid=names)
        active_func = syntax.Let(
            syntax.SortedVar(name, func.sort), ap_func,
            syntax.New(syntax.Apply(actives[syntax.get_decl_from_sort(func.sort)].name, [syntax.Id(name)])))
        conjs.append(syntax.Forall([syntax.SortedVar(name, None) for name in names],
                                   syntax.Implies(syntax.And(*func_conjs), active_func)))

    # (relativized) axioms hold after relaxation
    for axiom in prog.axioms():
        if not syntax.is_universal(axiom.expr):
            conjs.append(syntax.relativize_quantifiers(actives, axiom.expr))

    # derived relations have the same interpretation on the active domain
    for rel in prog.derived_relations():
        names = []
        rel_conjs = []
        for arg_sort in rel.arity:
            arg_sort_decl = syntax.get_decl_from_sort(arg_sort)
            name = prog.scope.fresh(arg_sort_decl.name[0].upper(),
                                    also_avoid=names)
            names.append(name)
            rel_conjs.append(syntax.Apply(actives[arg_sort_decl].name, [syntax.Id(name)]))
        ap_rel = syntax.Apply(rel.name, [syntax.Id(name) for name in names])
        conjs.append(syntax.Forall([syntax.SortedVar(name, None) for name in names],
                                   syntax.Implies(syntax.And(*rel_conjs),
                                                  syntax.Iff(syntax.New(ap_rel), ap_rel))))

    return syntax.DefinitionDecl(is_public_transition=True, num_states=2, name=decrease_name,
                                 params=[], mods=mods, expr=syntax.And(*conjs))


def relax_actives_action_chunk(scope: syntax.Scope, actives: Dict[syntax.SortDecl, syntax.RelationDecl]) \
        -> Tuple[List[syntax.ModifiesClause], List[Expr]]:
    new_mods = []
    new_conjs = []

    for sort, active_rel in actives.items():
        name = scope.fresh(sort.name[0].upper())
        ap = syntax.Apply(active_rel.name, [syntax.Id(name)])
        expr = syntax.Forall([syntax.SortedVar(name, None)],
                             syntax.Implies(syntax.New(ap), ap))
        new_conjs.append(expr)
        new_mods.append(syntax.ModifiesClause(actives[sort].name))

    return new_mods, new_conjs


class RelationFact:
    def __init__(self, rel: syntax.RelationDecl, els: List[str], polarity: bool):
        self._rel = rel
        self._els = els
        self._polarity = polarity

    def as_expr(self, els_trans: Callable[[str], str]) -> Expr:
        fact_free_vars = syntax.Apply(self._rel.name, [syntax.Id(els_trans(e)) for e in self._els])
        if not self._is_positive():
            fact_free_vars = syntax.Not(fact_free_vars)
        return fact_free_vars

    def involved_elms(self) -> List[str]:
        return self._els

    def _is_positive(self) -> bool:
        return self._polarity

    def __repr__(self) -> str:
        return "RelationFact(rel=%s, els=%s, polarity=%s)" % (self._rel, self._els, self._polarity)

    def __str__(self) -> str:
        return "%s(%s) = %s" % (self._rel.name, self._els, str(self._polarity))

class FunctionFact:
    def __init__(self, func: syntax.FunctionDecl, param_els: List[str], res_elm: str):
        self._func = func
        self._params_els = param_els
        self._res_elm = res_elm

    def as_expr(self, els_trans: Callable[[str], str]) -> Expr:
        e = syntax.AppExpr(self._func.name, [syntax.Id(els_trans(e)) for e in self._params_els])
        return syntax.Eq(e, syntax.Id(els_trans(self._res_elm)))

    def involved_elms(self) -> List[str]:
        return self._params_els + [self._res_elm]

    def __repr__(self) -> str:
        return "FunctionFact(func=%s, param_els=%s, res_elm=%s)" % (self._func, self._params_els, self._res_elm)

    def __str__(self) -> str:
        return "%s(%s) = %s" % (self._func.name, self._params_els, self._res_elm)

class InequalityFact:
    def __init__(self, lhs: str, rhs: str):
        self._lhs = lhs
        self._rhs = rhs

    def as_expr(self, els_trans: Callable[[str], str]) -> Expr:
        return syntax.Neq(syntax.Id(els_trans(self._lhs)),
                          syntax.Id(els_trans(self._rhs)))

    def involved_elms(self) -> List[str]:
        return [self._lhs, self._rhs]

    def __repr__(self) -> str:
        return "InequalityFact(lhs=%s, rhs=%s)" % (self._lhs, self._rhs)

    def __str__(self) -> str:
        return "%s ! %s" % (self._lhs, self._rhs)

def dict_val_from_rel_name(name: str, m: Dict[syntax.RelationDecl, T]) -> T:
    for r, v in m.items():
        if r.name != name:
            continue
        return v
    raise KeyError

def first_relax_step_idx(trns: Trace) -> int:
    first_relax_idx = trns.transitions.index('decrease_domain')
    assert first_relax_idx != -1, trns.transitions
    assert first_relax_idx + 1 < trns.num_states
    return first_relax_idx

def all_relax_step_idx(trns: Trace) -> List[int]:
    res = [i for (i, x) in enumerate(trns.transitions) if x == 'decrease_domain']
    assert len(res) > 0
    assert all(i + 1 < trns.num_states for i in res)
    return res

def active_rel(sort: syntax.SortDecl) -> syntax.RelationDecl:
    res = syntax.the_program.scope.get_relation('active_%s' % sort.name)
    assert res is not None
    return res

def active_rel_by_sort(prog: syntax.Program) -> Dict[syntax.SortDecl, syntax.RelationDecl]:
    return dict((sort, active_rel(sort)) for sort in prog.sorts())

def active_var(name: str, sort_name: str) -> syntax.Expr:
    return syntax.Apply('active_%s' % sort_name, [syntax.Id(name)])

def closing_qa_cycle(
        prog: syntax.Program, free_vars_sorts: List[syntax.SortDecl],
        existentially_quantified_sorts: List[syntax.SortDecl]
) -> bool:
    qa_graph = translator.decls_quantifier_alternation_graph(prog, [])
    assert networkx.is_directed_acyclic_graph(qa_graph)

    for asort in free_vars_sorts:
        for esort in existentially_quantified_sorts:
            qa_graph.add_edge(asort.name, esort.name)

    return not networkx.is_directed_acyclic_graph(qa_graph)

def is_rel_blocking_relax(trns: Trace,
                          derived_rel: Tuple[List[Tuple[syntax.SortedVar, str]], Expr]) -> bool:
    relax_idxs = all_relax_step_idx(trns)
    assert len(relax_idxs) > 0
    return any(is_rel_blocking_relax_step(trns, idx, derived_rel)
               for idx in relax_idxs)

def is_rel_blocking_relax_step(
        trns: Trace, idx: int,
        derived_rel: Tuple[List[Tuple[syntax.SortedVar, str]], Expr]
) -> bool:
    # TODO: probably can obtain the sort from the sortedvar when not using pickle
    free_vars, derived_relation_formula = derived_rel
    free_vars_active_clause = syntax.And(*(active_var(v.name, sort_name) for (v, sort_name) in free_vars))

    diffing_formula = syntax.Exists([v for (v, _) in free_vars],
                                    syntax.And(syntax.And(free_vars_active_clause,
                                                          derived_relation_formula),
                                               syntax.New(syntax.And(free_vars_active_clause,
                                                                     syntax.Not(derived_relation_formula)))))

    with syntax.the_program.scope.fresh_stack():
        with syntax.the_program.scope.n_states(2):
            resolver.resolve_expr(syntax.the_program.scope, diffing_formula, syntax.BoolSort)

    res = trns.eval(diffing_formula, idx)
    assert isinstance(res, bool)
    return cast(bool, res)

def derived_rels_candidates_from_trace(
        trns: Trace, more_traces: List[Trace],
        max_conj_size: int, max_free_vars: int
) -> List[Tuple[List[syntax.SortedVar], Expr]]:
    first_relax_idx = first_relax_step_idx(trns)
    pre_relax_state = trns.as_state(first_relax_idx)
    post_relax_state = trns.as_state(first_relax_idx + 1)
    assert pre_relax_state.univs() == post_relax_state.univs()

    # relaxed elements
    relaxed_elements = []
    for sort, univ in pre_relax_state.univs().items():
        active_rel_name = 'active_' + sort.name         # TODO: de-duplicate
        pre_active_interp = dict_val_from_rel_name(active_rel_name, pre_relax_state.rel_interp())
        post_active_interp = dict_val_from_rel_name(active_rel_name, post_relax_state.rel_interp())
        pre_active_elements = [tup[0] for (tup, b) in pre_active_interp if b]
        post_active_elements = [tup[0] for (tup, b) in post_active_interp if b]
        assert set(post_active_elements).issubset(set(pre_active_elements))

        for relaxed_elem in utils.OrderedSet(pre_active_elements) - set(post_active_elements):
            relaxed_elements.append((sort, relaxed_elem))

    # pre-relaxation step facts concerning at least one relaxed element (other to be found by UPDR)
    relevant_facts: List[Union[RelationFact, FunctionFact, InequalityFact]] = []

    for rel, rintp in pre_relax_state.rel_interp().items():
        for rfact in rintp:
            (elms, polarity) = rfact
            relation_fact = RelationFact(rel, elms, polarity)
            if set(relation_fact.involved_elms()) & set(ename for (_, ename) in relaxed_elements):
                relevant_facts.append(relation_fact)

    for func, fintp in pre_relax_state.func_interp().items():
        for ffact in fintp:
            (els_params, els_res) = ffact
            function_fact = FunctionFact(func, els_params, els_res)
            if set(function_fact.involved_elms()) & set(ename for (_, ename) in relaxed_elements):
                relevant_facts.append(function_fact)

    for sort, elm in relaxed_elements:  # other inequalities presumably handled by UPDR
        for other_elm in pre_relax_state.univs()[sort]:
            if other_elm == elm:
                continue
            relevant_facts.append(InequalityFact(elm, other_elm))

    # facts blocking this specific relaxation step
    diff_conjunctions = []
    candidates_cache: Set[str] = set()
    for fact_lst in itertools.combinations(relevant_facts, max_conj_size):
        elements = utils.OrderedSet(itertools.chain.from_iterable(fact.involved_elms() for fact in fact_lst))
        relaxed_elements_relevant = [elm for (_, elm) in relaxed_elements if elm in elements]
        vars_from_elm = dict((elm, syntax.SortedVar(syntax.the_program.scope.fresh("v%d" % i), None))
                             for (i, elm) in enumerate(elements))
        parameter_elements = elements - set(relaxed_elements_relevant)
        if len(parameter_elements) > max_free_vars:
            continue

        conjuncts = [fact.as_expr(lambda elm: vars_from_elm[elm].name) for fact in fact_lst]

        # for elm, var in vars_from_elm.items():
        # TODO: make the two loops similar
        # TODO: ! use syntax.relativize_quantifiers instead
        for elm in relaxed_elements_relevant:
            var = vars_from_elm[elm]
            sort = pre_relax_state.element_sort(elm)
            active_element_conj = syntax.Apply('active_%s' % sort.name, [syntax.Id(var.name)])
            conjuncts.append(active_element_conj)

        derived_relation_formula = syntax.Exists([vars_from_elm[elm]
                                                  for (_, elm) in relaxed_elements
                                                  if elm in vars_from_elm],
                                                 syntax.And(*conjuncts))

        if str(derived_relation_formula) in candidates_cache:
            continue
        candidates_cache.add(str(derived_relation_formula))

        if closing_qa_cycle(syntax.the_program,
                            [pre_relax_state.element_sort(elm) for elm in parameter_elements],
                            [pre_relax_state.element_sort(elm) for elm in relaxed_elements_relevant]):
            # adding the derived relation would close a quantifier alternation cycle, discard the candidate
            continue

        # if trns.eval_double_vocab(diffing_formula, first_relax_idx):
        if is_rel_blocking_relax_step(
                trns, first_relax_idx,
                ([(vars_from_elm[elm], pre_relax_state.element_sort(elm).name) for elm in parameter_elements],
                 derived_relation_formula)):
            # if all(trs.eval_double_vocab(diffing_formula, first_relax_step_idx(trs)) for trs in more_traces):
            diff_conjunctions.append(([vars_from_elm[elm] for elm in parameter_elements],
                                      derived_relation_formula))

    return diff_conjunctions

def replace_relaxation_action(prog: syntax.Program, new_relax_action: syntax.DefinitionDecl) -> syntax.Program:
    old_relaxation_action = prog.scope.get('decrease_domain')
    decls = [decl for decl in prog.decls if decl != old_relaxation_action]
    decls.append(new_relax_action)
    return syntax.Program(decls)


def transition_decl_from_name(transition_name: str) -> syntax.TraceTransitionDecl:
    NO_ARGS = None
    transition_decl = syntax.TransitionCall(transition_name, NO_ARGS)
    return syntax.TraceTransitionDecl(syntax.TransitionCalls([transition_decl]))

def relativized_assert_decl(formula: Union[Expr, Diagram]) -> syntax.AssertDecl:
    if isinstance(formula, Diagram):
        expr = formula.to_ast()
    else:
        expr = formula
    relativized_expr = syntax.relativize_quantifiers(active_rels_mapping(), expr)
    return syntax.AssertDecl(relativized_expr)

def active_rels_mapping() -> Mapping[syntax.SortDecl, syntax.RelationDecl]:
    # TODO: should be read from the relaxation / the program, not fixed.
    # TODO: duplicated from relaxed_program()
    actives: Dict[syntax.SortDecl, syntax.RelationDecl] = {}
    prog = syntax.the_program

    for sort in prog.sorts():
        name = 'active_' + sort.name  # prog.scope.fresh('active_' + sort.name)
        r = syntax.RelationDecl(name, arity=[syntax.UninterpretedSort(sort.name)],
                                mutable=True, derived=None, annotations=[])
        actives[sort] = r

    return actives

def diagram_trace_to_explicitly_relaxed_trace_decl(trace: RelaxedTrace, ending_property: Expr) -> syntax.TraceDecl:
    trace = list(reversed(trace))

    components: List[syntax.TraceComponent] = []
    assert len(trace) > 1
    _, first_diag = trace[0]
    components.append(relativized_assert_decl(first_diag))

    for pre, post in zip(trace, trace[1:]):
        t, pre_diag = pre
        assert t is not None
        _, post_diag = post

        assert isinstance(pre_diag, Diagram)
        assert isinstance(post_diag, Diagram)

        actual_transition = transition_decl_from_name(t.name)
        components.append(actual_transition)

        assert len(pre_diag.vs()) >= len(post_diag.vs())
        if len(pre_diag.vs()) != len(post_diag.vs()):
            components.append(transition_decl_from_name('decrease_domain'))  # TODO: make non-hardcoded

    # _, last_diag = trace[-1]
    components.append(relativized_assert_decl(ending_property))

    return syntax.TraceDecl(components, True)

def diagram_trace_to_explicitly_relaxed_trace(trace: RelaxedTrace, safety: Sequence[syntax.InvariantDecl]) -> None:
    relaxed_prog = relaxed_program(syntax.the_program)

    with syntax.prog_context(relaxed_prog):
        s = Solver()

        end_expr = syntax.Not(syntax.And(*(invd.expr for invd in safety)))
        with syntax.the_program.scope.n_states(1):
            resolver.resolve_expr(syntax.the_program.scope, end_expr, syntax.BoolSort)
        trace_decl = diagram_trace_to_explicitly_relaxed_trace_decl(trace, end_expr)
        with syntax.the_program.scope.n_states(1):
            resolver.resolve_tracedecl(syntax.the_program.scope, trace_decl)

        print(trace_decl)

        res = bmc_trace(relaxed_prog, trace_decl, s, lambda slvr, ks: logic.check_solver(slvr, ks, minimize=True))
        print(res)
        assert False


class Z3RelaxedSemanticsTranslator(translator.Z3Translator):
    # ODED: talk to James about it. There should be another way to implement relaxed traces other than
    #       inheriting from Z3Translator...
    def __init__(self, scope: syntax.Scope[z3.ExprRef], num_states: int) -> None:
        self._active_rels_mapping: Dict[syntax.SortDecl, syntax.RelationDecl] = {}
        self._generate_active_rels(scope)

        self._active_scope = copy.deepcopy(scope)
        for active_rel in self._active_rels_mapping.values():
            self._active_scope.add_relation(active_rel)

        self._t = translator.Z3Translator(self._active_scope, num_states)
        self._prog = syntax.the_program

    def _generate_active_rels(self, scope: syntax.Scope) -> None:
        for sort in scope.known_sorts():
            active_name = scope.fresh('active_%s' % sort.name)
            # TODO: is there a better way to get Sort out of SortDecl?
            sort_not_decl = syntax.UninterpretedSort(sort.name)
            resolver.resolve_sort(scope, sort_not_decl)
            active_rel = syntax.RelationDecl(active_name, arity=[sort_not_decl],
                                             mutable=True, derived=None, annotations=[])
            self._active_rels_mapping[sort] = active_rel

    def translate_expr(self, expr: Expr) -> z3.ExprRef:
        rel_expr = syntax.relativize_quantifiers(self._active_rels_mapping, expr)
        res = self._t.translate_expr(rel_expr)
        return res

    def translate_transition(self, t: syntax.DefinitionDecl, index: int = 0) -> z3.ExprRef:
        new_decl = relativize_decl(t, self._active_rels_mapping, self._active_scope, inline_relax_actives=True)
        # TODO: hack! relativize_decl doesn't do this, so the expression can be non-closed.
        # TODO: Should it generate & use an extended scope?
        resolver.resolve_declcontainingexpr(self._active_scope, new_decl)
        res = self._t.translate_transition(new_decl, index)
        return res

def consts_exist_axioms(prog: syntax.Program) -> List[Expr]:
    res = []

    for c in prog.constants():
        name = prog.scope.fresh('e_%s' % c.name)
        ax = syntax.Exists([syntax.SortedVar(name, c.sort)],
                           syntax.Eq(syntax.Id(c.name), syntax.Id(name)))
        with prog.scope.n_states(1):
            resolver.resolve_expr(prog.scope, ax, syntax.BoolSort)
        res.append(ax)

    return res

def functions_total_axioms(prog: syntax.Program) -> List[Expr]:
    res = []

    for func in prog.functions():
        # TODO: generation of part of the formula duplicated from relaxation_action_def.
        # TODO: would be best to beef up the expression-generation library
        names: List[str] = []
        params = []
        for arg_sort in func.arity:
            arg_sort_decl = syntax.get_decl_from_sort(arg_sort)
            name = prog.scope.fresh(arg_sort_decl.name[0].upper(),
                                    also_avoid=names)
            names.append(name)
            params.append(syntax.SortedVar(name, arg_sort))
        ap_func = syntax.Apply(func.name, [syntax.Id(v.name) for v in params])

        name = prog.scope.fresh('y', also_avoid=names)

        ax = syntax.Forall(params,
                           syntax.Exists([syntax.SortedVar(name, func.sort)],
                                         syntax.Eq(syntax.Id(name), ap_func)))
        with prog.scope.n_states(1):
            resolver.resolve_expr(prog.scope, ax, syntax.BoolSort)

        res.append(ax)

    return res

def relaxed_semantics_solver(prog: syntax.Program) -> logic.Solver:
    # reassert_axioms=True ensures that axioms continue to hold active relations change
    # additional_mutable_axioms guarantee that constants are always active
    # (through a relaxation of asserting the existence of an element that equals them),
    # and that functions are always total (through a relaxation of this axiom)
    return logic.Solver(translator_factory=lambda s, k: Z3RelaxedSemanticsTranslator(s, k),
                        reassert_axioms=True,
                        additional_mutable_axioms=consts_exist_axioms(prog) + functions_total_axioms(prog))

def check_relaxed_bmc(safety: Expr, depth: int, preconds: Optional[Iterable[Expr]] = None,
                      minimize: Optional[bool] = None) -> Optional[Trace]:
    prog = syntax.the_program
    return logic.check_bmc(relaxed_semantics_solver(prog),
                           safety, depth, preconds, minimize)
