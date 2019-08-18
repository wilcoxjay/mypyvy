import syntax
import utils
from logic import Trace
from syntax import Expr
from utils import Set

import itertools
from typing import List, Callable, Union, Dict, TypeVar

T = TypeVar('T')

class RelationFact(object):
    def __init__(self, rel: syntax.RelationDecl, els: List[str], polarity: bool):
        self._rel = rel
        self._els = els
        self._polarity = polarity

    def as_expr(self, els_trans: Callable[[str],str]) -> Expr:
        fact_free_vars = syntax.Apply(self._rel.name, [syntax.Id(None, els_trans(e)) for e in self._els])
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

class FunctionFact(object):
    def __init__(self, func: syntax.FunctionDecl, param_els: List[str], res_elm: str):
        self._func = func
        self._params_els = param_els
        self._res_elm = res_elm

    def as_expr(self, els_trans: Callable[[str],str]) -> Expr:
        e = syntax.AppExpr(None, self._func.name, [syntax.Id(None, els_trans(e)) for e in self._params_els])
        return syntax.Eq(e, syntax.Id(None, els_trans(self._res_elm)))

    def involved_elms(self) -> List[str]:
        return self._params_els + [self._res_elm]

    def __repr__(self) -> str:
        return "FunctionFact(func=%s, param_els=%s, res_elm=%s)" % (self._func, self._params_els, self._res_elm)

    def __str__(self) -> str:
        return "%s(%s) = %s" % (self._func.name, self._params_els, self._res_elm)

class InequalityFact(object):
    def __init__(self, lhs: str, rhs: str):
        self._lhs = lhs
        self._rhs = rhs

    def as_expr(self, els_trans: Callable[[str],str]) -> Expr:
        return syntax.Neq(syntax.Id(None, els_trans(self._lhs)),
                          syntax.Id(None, els_trans(self._rhs)))

    def involved_elms(self) -> List[str]:
        return [self._lhs, self._rhs]

    def __repr__(self) -> str:
        return "InequalityFact(lhs=%s, rhs=%s)" % (self._lhs, self._rhs)

    def __str__(self) -> str:
        return "%s ! %s" % (self._lhs, self._rhs)

def dict_val_from_rel_name(name: str, m: Dict[syntax.RelationDecl,T]) -> T:
    for r,v in m.items():
        if r.name != name:
            continue
        return v
    raise KeyError

def first_relax_step_idx(trns: Trace) -> int:
    first_relax_idx = trns.transitions.index('decrease_domain')
    assert first_relax_idx != -1, trns.transitions
    assert first_relax_idx + 1 < len(trns.keys)
    return first_relax_idx

def active_var(name: str, sort: syntax.SortDecl) -> syntax.Expr:
    return syntax.Apply('active_%s' % sort.name, [syntax.Id(None, name)])


def derived_rels_candidates_from_trace(trns: Trace, max_conj_size: int, max_free_vars: int) -> List[Expr]:
    first_relax_idx = first_relax_step_idx(trns)
    pre_relax_state = trns.as_state(first_relax_idx)
    post_relax_state = trns.as_state(first_relax_idx + 1)
    assert pre_relax_state.univs == post_relax_state.univs


    # relaxed elements
    relaxed_elements = []
    for sort, univ in pre_relax_state.univs.items():
        active_rel_name = 'active_' + sort.name         # TODO: de-duplicate
        pre_active_interp = dict_val_from_rel_name(active_rel_name, pre_relax_state.rel_interp)
        post_active_interp = dict_val_from_rel_name(active_rel_name, post_relax_state.rel_interp)
        pre_active_elements = [tup[0] for (tup, b) in pre_active_interp if b]
        post_active_elements = [tup[0] for (tup, b) in post_active_interp if b]
        assert set(post_active_elements).issubset(set(pre_active_elements))

        for relaxed_elem in utils.OrderedSet(pre_active_elements) - set(post_active_elements):
            relaxed_elements.append((sort, relaxed_elem))

    # pre-relaxation step facts concerning at least one relaxed element (other to be found by UPDR)
    relevant_facts: List[Union[RelationFact,FunctionFact,InequalityFact]] = []

    for rel, rintp in pre_relax_state.rel_interp.items():
        for rfact in rintp:
            (elms, polarity) = rfact
            relation_fact = RelationFact(rel, elms, polarity)
            if set(relation_fact.involved_elms()) & set(ename for (_, ename) in relaxed_elements):
                relevant_facts.append(relation_fact)

    for func, fintp in pre_relax_state.func_interp.items():
        for ffact in fintp:
            (els_params, els_res) = ffact
            function_fact = FunctionFact(func, els_params, els_res)
            if set(function_fact.involved_elms()) & set(ename for (_, ename) in relaxed_elements):
                relevant_facts.append(function_fact)

    for sort, elm in relaxed_elements: # other inequalities presumably handled by UPDR
        for other_elm in pre_relax_state.univs[sort]:
            if other_elm == elm:
                continue
            relevant_facts.append(InequalityFact(elm, other_elm))

    # facts blocking this specific relaxation step
    diff_conjunctions = []
    candidates_cache: Set[str] = set()
    for fact_lst in itertools.combinations(relevant_facts, max_conj_size):
        elements = utils.OrderedSet(itertools.chain.from_iterable(fact.involved_elms() for fact in fact_lst))
        relaxed_elements_relevant = [elm for (_, elm) in relaxed_elements if elm in elements]
        vars_from_elm = dict((elm, syntax.SortedVar(None, syntax.the_program.scope.fresh("v%d" % i), None))
                                for (i, elm) in enumerate(elements))
        parameter_elements = elements - set(relaxed_elements_relevant)
        if len(parameter_elements) > max_free_vars:
            continue

        conjuncts = [fact.as_expr(lambda elm: vars_from_elm[elm].name) for fact in fact_lst]

        # for elm, var in vars_from_elm.items():
        # TODO: make the two loops similar
        for elm in relaxed_elements_relevant:
            var = vars_from_elm[elm]
            sort = pre_relax_state.element_sort(elm)
            active_element_conj = syntax.Apply('active_%s' % sort.name, [syntax.Id(None, var.name)])
            conjuncts.append(active_element_conj)

        free_vars_active_clause = syntax.And(*(active_var(vars_from_elm[elm].name, pre_relax_state.element_sort(elm))
                                             for elm in parameter_elements))

        derived_relation_formula = syntax.Exists([vars_from_elm[elm]
                                                  for (_, elm) in relaxed_elements
                                                  if elm in vars_from_elm],
                                                 syntax.And(*conjuncts))

        diffing_formula = syntax.Exists([vars_from_elm[elm] for elm in parameter_elements],
                                        syntax.And(syntax.Old(syntax.And(free_vars_active_clause,
                                                                         derived_relation_formula)),
                                                   syntax.And(free_vars_active_clause,
                                                              syntax.Not(derived_relation_formula))))

        with syntax.the_program.scope.two_state(twostate=True): # TODO: what is this doing? probably misusing
            diffing_formula.resolve(syntax.the_program.scope, syntax.BoolSort)

        if str(diffing_formula) in candidates_cache:
            continue
        candidates_cache.add(str(diffing_formula))

        if trns.eval_double_vocab(diffing_formula, first_relax_idx):
            diff_conjunctions.append(derived_relation_formula)

    return diff_conjunctions
