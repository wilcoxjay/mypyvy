
import time
import argparse
import itertools
import re
import random
import math
from itertools import product, chain, combinations, repeat
from collections import defaultdict

from syntax import *
from logic import *
from pd import check_two_state_implication

try:
    import separators  # type: ignore # TODO: remove this after we find a way for travis to have folseparators
    import separators.timer
except ModuleNotFoundError:
    pass

from typing import TypeVar, Iterable, FrozenSet, Union, Callable, Generator, Set, Optional, cast, Type, Collection

PDState = Tuple[Trace, int]

def eval_predicate(s: PDState, p: Expr) -> bool:
    r = s[0].as_state(s[1]).eval(p)
    assert isinstance(r, bool)
    return r

class FOLSeparator(object):
    '''Class used to call into the folseparators code'''
    def __init__(self, states: List[PDState]) -> None:
        prog = syntax.the_program
        self.states = states
        self.ids: Dict[int, int] = {}
        self.sig = separators.logic.Signature()
        def sort_to_name(s: Sort) -> str:
            assert isinstance(s, UninterpretedSort)
            return s.name
        for d in prog.decls:
            if isinstance(d, SortDecl):
                self.sig.sorts.add(d.name)
            elif isinstance(d, ConstantDecl):
                self.sig.constants[d.name] = sort_to_name(d.sort)
            elif isinstance(d, RelationDecl):
                self.sig.relations[d.name] = list(sort_to_name(s) for s in d.arity)
            elif isinstance(d, FunctionDecl):
                self.sig.functions[d.name] = (list(sort_to_name(s) for s in d.arity), sort_to_name(d.sort))
        self.sig.finalize_sorts()
        S = separators.separate.HybridSeparator if utils.args.separator == 'hybrid' else\
            separators.separate.GeneralizedSeparator if utils.args.separator == 'generalized' else\
            separators.separate.SeparatorNaive
        self.separator = S(self.sig, logic=utils.args.logic, quiet=True)

    def _state_id(self, i: int) -> int:
        assert 0 <= i < len(self.states)
        if i not in self.ids:
            # add a new state
            m = self.state_to_model(self.states[i])
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
            p = self.formula_to_predicate(f)
            for i in pos:
               assert eval_predicate(self.states[i], p)
            for i in neg:
               assert not eval_predicate(self.states[i], p)
            for i, j in imp:
               assert (not eval_predicate(self.states[i], p)) or eval_predicate(self.states[j], p)
            return p

    def state_to_model(self, s: PDState) -> separators.logic.Model:
        t, i = s
        relations = dict(itertools.chain(t.immut_rel_interps.items(), t.rel_interps[i].items()))
        constants = dict(itertools.chain(t.immut_const_interps.items(), t.const_interps[i].items()))
        functions = dict(itertools.chain(t.immut_func_interps.items(), t.func_interps[i].items()))
        m = separators.logic.Model(self.sig)
        for sort in sorted(t.univs.keys(),key=str):
            for e in t.univs[sort]:
                m.add_elem(e, sort.name)
        for cd, e in constants.items():
            res = m.add_constant(cd.name, e)
            assert res
        for rd in relations:
            for es, v in relations[rd]:
                if v:
                    m.add_relation(rd.name, es)
        for fd in functions:
            for es, e in functions[fd]:
                m.add_function(fd.name, es, e)
        return m

    def formula_to_predicate(self, f: separators.logic.Formula) -> Expr:
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


def check_initial(solver: Solver, p: Expr) -> Optional[Trace]:
    prog = syntax.the_program
    inits = tuple(init.expr for init in prog.inits())
    m = check_implication(solver, inits, [p])
    if m is None:
        return None
    return Trace.from_z3([KEY_ONE], m)

def check_safe(solver: Solver, ps: List[Expr]) -> Optional[Trace]:
    '''Used only in fol_ice, not cached'''
    prog = syntax.the_program
    safety = tuple(inv.expr for inv in prog.invs() if inv.is_safety)
    z3m = check_implication(solver, ps, safety)
    if z3m is not None:
        s = Trace.from_z3([KEY_ONE], z3m)
        print(f'Found bad state satisfying {" and ".join(map(str,ps))}:')
        print('-'*80 + '\n' + str(s) + '\n' + '-'*80)
        return s
    return None

def trace_pair_from_model(m: z3.ModelRef) -> Tuple[Trace, Trace]:
    old = Trace.from_z3([KEY_OLD], m)
    new = Trace.from_z3([KEY_NEW, KEY_OLD], m)
    return (old, new)

def check_two_state_implication_uncached(solver: Solver, ps: List[Expr], c: Expr, minimize: Optional[bool] = None, timeout: int = 0) -> Optional[Tuple[Trace, Trace]]:
    edge = check_two_state_implication_all_transitions_unknown_is_unsat(solver, old_hyps = ps, new_conc = c, minimize=minimize, timeout=timeout)
    return trace_pair_from_model(edge[0]) if edge is not None else None

def check_two_state_implication_generalized(
        s: Solver,
        trans: DefinitionDecl,
        old_hyps: Iterable[Expr],
        new_conc: Expr,
        minimize: Optional[bool] = None,
        timeout: int = 0,
) -> Tuple[z3.CheckSatResult, Optional[z3.ModelRef]]:
    with s:
        t = s.get_translator(KEY_NEW, KEY_OLD)
        for h in old_hyps:
            s.add(t.translate_expr(h, old=True))
        s.add(z3.Not(t.translate_expr(new_conc)))
        s.add(t.translate_transition(trans))

        print(f'check_two_state_implication_generalized: checking {trans.name}... ', end='')
        res = s.check(timeout=timeout)
        print(res)
        if res == z3.sat:
            return (z3.sat, s.model(minimize=minimize))
        return (res, None)



def cover(s: Sequence[Set[int]]) -> Sequence[int]:
    if len(s) == 0: return []
    m = len(set(y for ss in s for y in ss))
    covered: Set[int] = set()
    sets = list(s)
    indices = list(range(len(s)))
    covering = []
    while len(covered) != m:
        best = max(range(len(sets)), key = lambda t: len(sets[t].difference(covered)))
        covering.append(indices[best])
        covered.update(sets[best])
        del sets[best]
        del indices[best]
    return covering

class BlockTask(object):
    def __init__(self, is_must: bool, state: int, frame: int, parent: Optional['BlockTask'], heuristic: bool = False):
        self.is_must = is_must
        self.state = state
        self.frame = frame
        self.predecessors_eliminated = False
        self.child_count = 0
        self.heuristic_child_count = 0
        self.parent = parent
        if parent is not None:
            parent.child_count += 1
            if heuristic:
                parent.heuristic_child_count += 1
        self.sep: Optional[FOLSeparator] = None
        self.is_unsep = False
        self.imp_constraints: List[Tuple[int, int]] = []
        self.prior_predicates: List[Expr] = []
        self.prior_eval_cache: List[Tuple[Set[int], Set[int]]] = []
        self.ci_cache: Dict[Tuple[int, int], bool] = {}
        self.generalize_bound = -1
        self.heuristic = heuristic
        
    def destroy(self) -> None:
        if self.parent is not None:
            self.parent.child_count -= 1
            if self.heuristic:
                self.parent.heuristic_child_count -= 1
    def reset_prior(self) -> None:
        self.prior_predicates = []
        self.prior_eval_cache = []
        self.ci_cache = {}
    def __str__(self) -> str:
        t = f"[{'!' if self.is_must else '*' if not self.heuristic else '?'} F_{self.frame} s={self.state}]"
        if self.parent is not None:
            return f"{str(self.parent)} -> {t}"
        return t

class TaskScheduler(object):
    def __init__(self) -> None:
        self.tasks: List[BlockTask] = []
        self.states: Dict[int, int] = {}
    def destroy(self, task: BlockTask) -> None:
        destroyed = set([task])
        changed = True
        while changed:
            changed = False
            for t in self.tasks:
                if t.parent is not None and t.parent in destroyed and t not in destroyed:
                    destroyed.add(t)
                    changed = True
        self.tasks = [t for t in self.tasks if t not in destroyed]
        for t in destroyed:
            t.destroy()
            self.states[t.state] = self.states[t.state] - 1
    def add(self, task: BlockTask) -> None:
        self.tasks.append(task)
        self.states[task.state] = self.states.get(task.state, 0) + 1
    def state_has_task(self, state: int) -> bool:
        return state in self.states and self.states[state] > 0
    def __iter__(self) -> Iterator[BlockTask]:
        return iter(self.tasks)
    def get_next(self) -> Optional[BlockTask]:
        def heuristic(t: BlockTask) -> bool:
            if t.heuristic: return True
            if t.parent is not None: return heuristic(t.parent)
            return False
        should_be_heuristic = random.choice([True, False])
        active_tasks = [tt for tt in self.tasks if tt.child_count - tt.heuristic_child_count == 0 and (heuristic(tt) == should_be_heuristic)]
        if len(active_tasks) == 0:
            should_be_heuristic = not should_be_heuristic
            active_tasks = [tt for tt in self.tasks if tt.child_count - tt.heuristic_child_count == 0 and (heuristic(tt) == should_be_heuristic)]
        random.shuffle(active_tasks)
        return active_tasks[0] if len(active_tasks) > 0 else None


def fol_ic3(solver: Solver) -> None:
    prog = syntax.the_program

    system_unsafe  = False
    predicates: List[Expr] = []
    frame_numbers: List[int] = [] # for each predicate, what is the highest frame?
    frame_n: int = 1 # highest frame

    def frame_predicates_indices(i: int) -> List[int]:
        return [p for p,f in enumerate(frame_numbers) if i <= f]
    def frame_predicates(i: int) -> List[Expr]:
        return [predicates[x] for x in frame_predicates_indices(i)]
    def add_predicate_to_frame(p: Expr, f: int) -> int:
        for i in range(len(predicates)):
            if p == predicates[i]:
                frame_numbers[i] = max(frame_numbers[i], f)
                return i
        i = len(predicates)
        predicates.append(p)
        frame_numbers.append(f)
        return i

    initial_states: List[int] = []
    reachability: Dict[int, Optional[int]] = {} # none means truly reachable
    K_bound = 0
    K_limit = 0
    states: List[PDState] = []
    transitions: List[Tuple[int,int]] = []
    eval_cache: Dict[Tuple[int,int], bool] = {}

    def add_initial(s: PDState) -> int:
        i = len(states)
        states.append(s)
        initial_states.append(i)
        reachability[i] = None
        return i
    def add_state(s: PDState) -> int:
        i = len(states)
        states.append(s)
        return i       
    def add_transition(pre: int, post: int) -> None:
        transitions.append((pre, post))

    def eval_pred_state(pred_idx: int, state_idx: int) -> bool:
        if (pred_idx, state_idx) not in eval_cache:
            eval_cache[(pred_idx, state_idx)] = eval_predicate(states[state_idx], predicates[pred_idx])
        return eval_cache[(pred_idx, state_idx)]
        
    def frame_states_indices(frame:int) -> Sequence[int]:
        pred_indices = frame_predicates_indices(frame)
        return [i for i, s in enumerate(states) if all(eval_pred_state(p, i) for p in pred_indices)]
    def frame_states(frame:int) -> Sequence[PDState]:
        return [states[a] for a in frame_states_indices(frame)]
    
    def frame_transitions_indices(frame:int) -> Sequence[Tuple[int, int]]:
        pred_indices = frame_predicates_indices(frame)
        return [(a, b) for a, b in transitions if all(eval_pred_state(p, a) for p in pred_indices)]
    def frame_transitions(frame:int) -> Sequence[Tuple[PDState, PDState]]:
        return [(states[a], states[b]) for a, b in frame_transitions_indices(frame)]
    def abstractly_reachable() -> Sequence[int]:
        return tuple(x for x, k in reachability.items() if k is None or k >= K_bound)
    def lower_bound_reachability(state: int, bound: Optional[int]) -> None:
        c = reachability.get(state, 0)
        reachability[state] = (None if c is None or bound is None else max(bound, c))
        print(f"State {state} is reachable at {reachability[state]}")

    tasks = TaskScheduler()
    def process_task() -> bool:
        nonlocal tasks, system_unsafe, K_bound
        
        t = tasks.get_next()
        if t is None:
            print("Couldn't find leaf task")
            return False
            
        print(f"Working on {t.state} in frame {t.frame}; {t}")
        if not all(eval_pred_state(p_i, t.state) for p_i in frame_predicates_indices(t.frame)):
            print(f"State {t.state} blocked in F_{t.frame}")
            tasks.destroy(t)
            return True
        
        for inv in prog.invs():
            if inv.name is not None:
                print(f" - {'T' if eval_predicate(states[t.state], inv.expr) else 'F'} [{inv.name}]")

        if t.frame == 0 or (t.state in abstractly_reachable()):
            # because of the previous if check, we know t.state is an initial state if frame == 0 and reachable otherwise
            if t.is_must:
                if K_bound < K_limit:
                    K_bound += 1
                    for t in tasks:
                        t.is_unsep = False # Need to reset this flag, which is cached state depending on K_bound
                    print(f"[IC3] Increasing K_bound to {K_bound}")
                    return True
                else:
                    print("[IC3] Transition system is UNSAFE!")
                    system_unsafe = True
                    return True
            else:
                if t.frame == 0:
                    lower_bound_reachability(t.state, None) # we've discovered a new initial state
                if t.parent is not None and (t.state, t.parent.state) in transitions:
                    lower_bound_reachability(t.parent.state, reachability[t.state])
                print(f"[IC3] Found reachable state {t.state} in F_{t.frame} (now have {len(reachability)} reachable states)")
                tasks.destroy(t)
                return True
        
        if not t.predecessors_eliminated:
            s = states[t.state]
            formula_to_block = Not(s[0].as_onestate_formula(s[1])) \
                           if utils.args.logic != "universal" else \
                           Not(s[0].as_diagram(s[1]).to_ast())
            edge = check_two_state_implication_uncached(solver, frame_predicates(t.frame-1), formula_to_block, minimize=False)
            if edge is None:
                t.predecessors_eliminated = True
                return True
            s_i = add_state((edge[0], 0))
            add_transition(s_i, t.state)
            assert t.frame > 0
            print(f"Eliminating predecessor {s_i} from F_{t.frame - 1}")
            tasks.add(BlockTask(t.is_must, s_i, t.frame - 1, t))
            return True
        
        if t.is_unsep:
            abs_reach = abstractly_reachable()
            remaining = len([i for (i,j) in t.imp_constraints if i not in abs_reach])
            print(f"[IC3] UNSEP {t} remaining={remaining}")

            for (i,j) in t.imp_constraints:
                if not all(eval_pred_state(p_i, i) for p_i in frame_predicates_indices(t.frame-1)):
                    # one of the constraints has been blocked by a new learned formula. The whole
                    # separation problem could now be satisfiable. Reset the flag on this task
                    print("Constraint blocked, computing new separability")
                    t.reset_prior()
                    t.is_unsep = False
                    return True
            for (i,j) in t.imp_constraints:
                if i in abs_reach:
                    continue
                print(f"Trying to block {i} in F_{t.frame-1}")
                tasks.add(BlockTask(False, i, t.frame-1, t))
                return True
            
            # couldn't block any, so this state is abstractly reachable
            print("[IC3] Found new (abstractly) reachable state")
            lower_bound_reachability(t.state, K_bound)
            return True

        if utils.args.inductive_generalize:
            inductive_generalize(t)
        else:
            generalize(t.state, t.frame)
        return True

    def print_learn_predicate(p: Expr) -> None:
        I_imp_p = "."
        p_imp_I = "."
        I = [i.expr for i in prog.invs()]
        if check_implication(solver, I, [p], minimize=False) is None:
            I_imp_p = ">"
        for i in I:
            if check_implication(solver, [p], [i], minimize=False) is None:
                p_imp_I = "<"
                break
        print(f"[IC3] Learned predicate (Ip{I_imp_p}{p_imp_I}): {p}")

    def generalize(s: int, i: int) -> None:
        print("Generalizing")
        # find p s.t. p is negative on s, init => p, F_i-1 => p, and F_i-1 => wp(p)
        sep = FOLSeparator(states)

        while True:
            print("Separating")
            pos = list(frame_states_indices(i-1)) + [x for y in frame_transitions_indices(i-1) for x in y]
            p = sep.separate(pos=pos, neg=[s], imp=[], complexity = K_bound)
            if p is None: raise RuntimeError("couldn't separate in generalize()")
            print(f"Candidate predicate is: {p}")

            # F_0 => p?
            state = check_initial(solver, p)
            if state is not None:
                print("Adding new initial state")
                add_initial((state, 0))
                continue
            # F_i-1 => p?
            cex = check_implication(solver, frame_predicates(i-1), [p])
            if cex is not None:
                print("Adding new free pre-state")
                t = Trace.from_z3([KEY_ONE], cex)
                add_state((t,0))
                continue
            # F_i-1 => wp(p)?
            tr = check_two_state_implication_uncached(solver, frame_predicates(i-1), p)
            if tr is not None:
                print("Adding new edge")
                s_i, s_j = add_state((tr[0],0)), add_state((tr[1],0))
                add_transition(s_i, s_j)
                continue

            print_learn_predicate(p)
            idx = add_predicate_to_frame(p, i)
            push()
            return

    def inductive_generalize(t: BlockTask) -> None:
        # find p s.t. p is negative on s, init => p, F_i-1 ^ p => wp(p)
        if t.sep is None:
            print("Inductive generalizing")
            t.sep = FOLSeparator(states)
            # Note, we may want to seed this set with some subset of the known frame transitions
            # which are most likely to constrain the solution, while avoiding adding all constraints
            # if there are very many of them.
            t.imp_constraints = []

        all_transitions = list(frame_transitions_indices(t.frame-1))
        # First, filter out elements of t.imp_constraints that are no longer active.
        t.imp_constraints = [x for x in t.imp_constraints if x in all_transitions]

        abs_reach = abstractly_reachable()

        oracle = next(i.expr for i in prog.invs() if i.name == 'hard')
        oracle_solves = all(eval_predicate(states[p], oracle) for p in abs_reach)\
            and all(not eval_predicate(states[n], oracle) for n in [t.state])\
            and all((not eval_predicate(states[a], oracle) or eval_predicate(states[b], oracle)) for (a,b) in t.imp_constraints)
        print(f"Oracle: {oracle}, works: {oracle_solves}")
        if not oracle_solves or K_bound < 3 or True:
            print(f"Separating in inductive_generalize |pos|={len(abs_reach)}, |imp|={len(t.imp_constraints)}")
            p = t.sep.separate(pos=abs_reach, neg=[t.state], imp = t.imp_constraints, complexity=K_bound)
        else:
            print(f"Using oracle predicate")
            p = oracle

        #p = t.sep.separate(pos=abs_reach, neg=[t.state], imp = t.imp_constraints, complexity=K_bound)
        if p is None:
            t.is_unsep = True
            # compute unsep core
            remaining = list(t.imp_constraints)
            core: List[Tuple[int,int]] = []
            while len(remaining) > 0:
                print(f"Checking unsep core {len(core)}/{len(remaining)}/{len(t.imp_constraints)}")
                if t.sep.separate(pos=abs_reach, neg=[t.state], imp = core + remaining[:-1], complexity=K_bound) is not None:
                    core.append(remaining[-1])
                remaining.pop()
            print (f"[IC3] Unsep core is size {len(core)} out of {len(t.imp_constraints)}")
            t.imp_constraints = core
            return
        
        p_respects_all_transitions = True
        for (s_i, s_j) in all_transitions:
            if (s_i, s_j) in t.imp_constraints:
                continue
            if eval_predicate(states[s_i], p) and not eval_predicate(states[s_j], p):
                p_respects_all_transitions = False
                t.imp_constraints.append((s_i, s_j))
                print_constraint_matrix(t)
                simplify_constraints(t, all_transitions, set(abs_reach))
                break # only add up to one transition at a time
        if not p_respects_all_transitions:
            # exit and go back up to the top of this function, but with new constraints
            print("Added cached transition to constraints")
            return
        
        print(f"Candidate predicate is: {p}")
        p_ind = len(t.prior_predicates)
        t.prior_predicates.append(p)
        t.prior_eval_cache.append((set(), set()))

        # init => p?
        state = check_initial(solver, p)
        if state is not None:
            print("Adding new initial state")
            add_initial((state, 0))
            return
        # F_i-1 ^ p => wp(p)?
        tr = find_generalized_implication(solver, t, frame_predicates(t.frame-1), p_ind)
        if tr is not None:
            print("Adding new edge")
            s_i, s_j = add_state((tr[0],0)), add_state((tr[1],0))
            add_transition(s_i, s_j)
            print(f"constriants = {len(t.imp_constraints)}")
            t.imp_constraints.append((s_i, s_j))
            print_constraint_matrix(t)
            simplify_constraints(t, all_transitions, set(abs_reach))
            print(f"constriants = {len(t.imp_constraints)}")
            return
        
        print_learn_predicate(p)
        idx = add_predicate_to_frame(p, t.frame)
        push()
        return



    from set_cover import cover
    def imp_constraints_covering(t:BlockTask, all_transitions: List[Tuple[int, int]], all_reachable: Set[int]) -> None:
        # Find a set cover of implication constraints that can erase 
        possiblities = [set(i for i,p in enumerate(t.prior_predicates) if task_prior_eval(t, i, a) and not task_prior_eval(t, i, b))
                        for tr_ind, (a,b) in enumerate(all_transitions)]
        possiblities.append(set(i for i,p in enumerate(t.prior_predicates) if any(not task_prior_eval(t, i, a) for a in all_reachable)))
        covering = cover(possiblities)
        t.imp_constraints = [all_transitions[i] for i in covering if i < len(all_transitions)]

    def simplify_constraints(t: BlockTask, all_transitions: List[Tuple[int, int]], all_reachable: Set[int]) -> None:
        #imp_constraints_covering(t, all_transitions, all_reachable)
        def sortfunc(transition: Tuple[int, int]) -> Tuple[int, int]:
            return (sum(1 if not task_prior_eval(t, i, transition[0]) else 0 for i in range(len(t.prior_predicates))),
                    sum(1 if not task_prior_eval(t, i, transition[1]) else 0 for i in range(len(t.prior_predicates))))
        B = 1 # 1 + math.floor(len(t.imp_constraints) / 15)
        if len(t.prior_predicates) >= 10 and len(t.imp_constraints) > 5 and t.heuristic_child_count < B:
            trs = list(sorted(filter(lambda tr: tr[0] not in all_reachable and not tasks.state_has_task(tr[0]), t.imp_constraints), key = sortfunc, reverse=True))
            if len(trs) > 0 and sortfunc(trs[0])[0] > 0:
                tasks.add(BlockTask(False, trs[0][0], t.frame-1, t, heuristic=True))
                print(f"Generating heuristic may-block constraint for {trs[0][0]} in frame {t.frame-1}")
        if t.generalize_bound < 0:
            t.generalize_bound = 1000000
        if len(t.prior_predicates) >= t.generalize_bound:
            t.generalize_bound = int(1 + t.generalize_bound * 2.0)
            print(f"Old length of imp_constraints is {len(t.imp_constraints)}, {t.imp_constraints}")
            force_generalize(t)
            # imp_constraints_covering(t, all_transitions, all_reachable)
            print(f"New length of imp_constraints is {len(t.imp_constraints)}, {t.imp_constraints}")
            imp_constraints_covering(t, list(frame_transitions_indices(t.frame-1)), all_reachable)
            print(f"After min imp_constraints is {len(t.imp_constraints)}, {t.imp_constraints}")

    def force_generalize(t: BlockTask) -> None:
        print("Force generalizing")
        timer = separators.timer.UnlimitedTimer()
        with timer:
            not_reachable_preds = set(i for i,p in enumerate(t.prior_predicates) if all(task_prior_eval(t, i, a) for a in abstractly_reachable()))
            remaining_preds = set(not_reachable_preds)
            more = []
            while len(remaining_preds) > 0:
                tr, eliminated = max(((tr, set(i for i in remaining_preds if task_prior_eval(t, i, tr[0]) and not task_prior_eval(t, i, tr[1]))) for tr in t.imp_constraints), key = lambda x: len(x[1]))
                initial_eliminated = len(eliminated)
                remaining_preds.difference_update(eliminated)
                for pi in remaining_preds:
                    if pi in eliminated: continue
                    ps = [t.prior_predicates[ei] for ei in eliminated] + [t.prior_predicates[pi]]
                    new_tr = check_two_state_implication_uncached(solver, frame_predicates(t.frame-1) + ps, Or(*ps), minimize=False, timeout=10000)
                    if new_tr is not None:
                        eliminated.add(pi)
                        s_i, s_j = add_state((new_tr[0],0)), add_state((new_tr[1],0))
                        add_transition(s_i, s_j)
                        tr = (s_i, s_j)
                        # add other predicates that are also blocked by this edge
                        for pj in remaining_preds:
                            if task_prior_eval(t, pj, s_i) and not task_prior_eval(t, pj, s_j):
                                eliminated.add(pj)
                more.append(tr)
                remaining_preds.difference_update(eliminated)
                true_eliminated = len(set(i for i in not_reachable_preds if task_prior_eval(t, i, tr[0]) and not task_prior_eval(t, i, tr[1])))
                print(f"Found new edge eliminating {len(eliminated)}/{true_eliminated} predicates out of {initial_eliminated}")
            t.imp_constraints.extend(more)
        
        print(f"Force generalized in {timer.elapsed():0.2f} sec")
        pass
    def task_prior_eval(t: BlockTask, ind: int, state: int) -> bool:
        """ Returns whether states[state] satisfies t.prior_predicates[ind], and caches the result"""
        (cache_true, cache_false) = t.prior_eval_cache[ind]
        if state in cache_true:
            return True
        if state in cache_false:
            return False
        value = eval_predicate(states[state], t.prior_predicates[ind])
        if value:
            cache_true.add(state)
        else:
            cache_false.add(state)
        return value

    def print_constraint_matrix(t: BlockTask) -> None:
        pass
        for (i,j) in t.imp_constraints:
            if all(eval_predicate(states[i], p.expr) for p in prog.invs()):
                print("I", end='')
            else:
                print(".", end='')
        print("")
        print("--- begin matrix ---")
        for ind, p in enumerate(t.prior_predicates):
            l = []
            for (i,j) in t.imp_constraints:
                a = task_prior_eval(t, ind, i)
                if a and not task_prior_eval(t, ind, j):
                    l.append('#')
                else:
                    l.append('+' if a else '-')
            print(''.join(l))
        print("--- end matrix ---")
    def push() -> None:
        made_changes = False
        for frame in range(frame_n):
            for i in range(len(frame_numbers)):
                if frame_numbers[i] == frame:
                    # try to push i
                    cex = check_two_state_implication(solver, frame_predicates(frame), predicates[i], minimize=False)
                    if cex is None:
                        frame_numbers[i] += 1
                        print(f"pushed {predicates[i]} to F_{frame_numbers[i]}")
                        made_changes = True
        if made_changes:
            pass
            #print("[IC3] Pushed predicates forward")
            #print_predicates()

    def print_predicates() -> None:
        print ("[IC3] ---- Frame summary")
        for f,p in sorted(zip(frame_numbers, predicates), key = lambda x: x[0]):
            print(f"[IC3] predicate {f} {p}")
        print("[IC3] ----")

    def print_summary() -> None:
        print(f"[IC3] time: {time.time() - start_time:0.3f} sec")
        print(f"[IC3] predicates considered: {len(predicates)}")
        print(f"[IC3] states considered: {len(states)}")
        print(f"[IC3] frames opened: {frame_n}")

    for init_decl in prog.inits():
        predicates.append(init_decl.expr)
        frame_numbers.append(0)
    K_limit = utils.args.max_complexity
    K_bound = 1 if utils.args.dynamic else K_limit
    print(f"[IC3] Inferring with K_bound = {K_bound} up to {K_limit} ({'dynamic' if utils.args.dynamic else 'static'}), with max clauses={utils.args.max_clauses}, depth={utils.args.max_depth}")
    start_time = time.time()
    while not system_unsafe:
        print(f"[time] Elapsed: {time.time()-start_time}")
        # Try to block things, if there are things to block
        if process_task():
            continue
    
        # Push any predicates that may have just been discovered
        push()
        
        # Check for bad states in the final frame.
        bad_state = check_safe(solver, frame_predicates(frame_n))
        if bad_state is not None:
            s_i = add_state((bad_state, 0))
            tasks.add(BlockTask(True, s_i, frame_n, None))
        else:
            print_predicates()
            print("Checking for an inductive frame")
            for inv_frame in reversed(range(1,frame_n + 1)):
                # skip frames identical to a previous one
                if not any(inv_frame == f for f in frame_numbers):
                    continue
                ps = frame_predicates(inv_frame)
                if all(check_two_state_implication(solver, ps, p, minimize=False) is None for p in ps):
                    
                    ps = frame_predicates(inv_frame)
                    print(f"[IC3] Found inductive invariant in frame {inv_frame}!")
                    for p in ps:
                        print(f"[IC3] invariant: {p}")
                    print_summary()
                    return
            print(f"[IC3] Expanding new frame {frame_n+1}")
            push()
            frame_n += 1
    # Loops exits if the protocol is unsafe. Still print statistics
    print_summary()



class EdgeGeneralizer(object):
    def __init__(self) -> None:
        self._prior_predicates : List[Expr] = []
        self._prop_solver: z3.Solver = z3.Solver()
        
        all_transitions = list(syntax.the_program.transitions())
        self._trans_id = dict(zip([t.name for t in all_transitions], range(len(all_transitions))))
        assert len(self._trans_id) == len(all_transitions) # ensure name is unique id
        
        self._prior_edges: List[Tuple[DefinitionDecl, List[int], List[int]]] = []

    def _to_exprs(self, l: List[int]) -> List[Expr]: return [self._prior_predicates[i] for i in l]
    def _pred_var(self, i: int, is_pre: bool) -> z3.ExprRef:
        return z3.Bool(f"P_{i}_{1 if is_pre else 0}")
    def _trans_var(self, trans: DefinitionDecl) -> z3.ExprRef:
        return z3.Bool(f"T_{self._trans_id[trans.name]}")

    def _vars_for_edge(self, trans: DefinitionDecl, pre: List[int], post: List[int]) -> List[z3.ExprRef]:
        return [self._trans_var(trans)] + [self._pred_var(i, True) for i in pre] + [self._pred_var(i, False) for i in post]
    
    def find_generalized_implication(self, solver: Solver, fp: List[Expr], p: Expr) -> Optional[Tuple[Trace, Trace]]:
        p_ind = len(self._prior_predicates)
        self._prior_predicates.append(p)
        tr = check_two_state_implication_uncached(solver, fp + [p], p, minimize=False)
        if tr is None: return None # early out if UNSAT
        all_transitions = list(syntax.the_program.transitions())
        tr_trans = all_transitions[0] # dummy

        def min_unsat_core(trans: DefinitionDecl, pre: List[int], post: List[int]) -> Tuple[List[int], List[int]]:
            pre, post = list(pre), list(post)
            min_core : Tuple[List[int], List[int]] = ([],[])
            print(f"Minimizing unsat core ({pre} => {post})...")
            while True:
                
                if len(pre) > 0:
                    c = pre.pop()
                    c = post.pop() # FOR UNIFORM PRE/POST
                    from_pre = True
                elif len(post) > 0:
                    c = post.pop()
                    from_pre = False
                else:
                    break

                candidate_pre, candidate_post = min_core[0] + pre, min_core[1] + post
                if len(candidate_pre) == 0 or len(candidate_post) == 0:
                    res = z3.sat # don't run empty queries. Helpful when |pre| = |post| = 1
                elif self._prop_solver.check(*self._vars_for_edge(trans, candidate_pre, candidate_post)) == z3.unsat:
                    res = z3.unsat
                else:
                    res, unused = check_two_state_implication_generalized(solver, trans, fp + self._to_exprs(candidate_pre), Or(*self._to_exprs(min_core[1] + post)), minimize=False, timeout=10000)
                    if res == z3.unsat:
                        self._prop_solver.add(z3.Not(z3.And(self._vars_for_edge(trans, candidate_pre, candidate_post))))
                if res == z3.sat:
                    if from_pre:
                        min_core[0].append(c)
                        min_core[1].append(c) # FOR UNIFORM PRE/POST
                    else:
                        min_core[1].append(c)
            print(f"Core is ({min_core[0]} => {min_core[1]})...")
            return min_core
        def check_sat(pre: List[int], post: List[int], skip: bool = True) -> bool: # returns true if satisfiable, and stores transition in `tr`
            nonlocal tr, tr_trans
            success = False
            for trans in all_transitions:
                if self._prop_solver.check(*self._vars_for_edge(trans, pre, post)) == z3.unsat:
                    print(f"Skipping known unsat for {trans.name}")
                    # skip the rest of the checks. We know that its unsat so don't need to add it again
                    continue
                res, tr_prime = check_two_state_implication_generalized(solver, trans, fp + self._to_exprs(pre), Or(*self._to_exprs(post)), minimize=False, timeout=10000)
                if tr_prime is not None:
                    tr = trace_pair_from_model(tr_prime)
                    tr_trans = trans
                    success = True
                    if skip: break
                elif res is z3.unknown:
                    if False:
                        # "normal way"
                        if skip: break
                    else:
                        # treat unknown like unsat. may block future possible edges but be faster
                        # probably should not try to minimize unsat (unknown?) core in this case
                        #pre_p, post_p = min_unsat_core(trans, pre, post)
                        pre_p, post_p = pre, post
                        print(f"Adding unknown UNSAT block for {trans.name}, [{' ^ '.join(map(str,pre_p))}] => [{' | '.join(map(str,post_p))}]")
                        self._prop_solver.add(z3.Not(z3.And(self._vars_for_edge(trans, pre_p, post_p))))
                elif res is z3.unsat:
                    pre_p, post_p = min_unsat_core(trans, pre, post)
                    print(f"Adding UNSAT for {trans.name}, [{' ^ '.join(map(str,pre_p))}] => [{' | '.join(map(str,post_p))}]")
                    self._prop_solver.add(z3.Not(z3.And(self._vars_for_edge(trans, pre_p, post_p))))
            return success
        
        # this call sets tr_trans correctly and also generates UNSATs for all transitions it can (due to skip=False).
        if not check_sat([p_ind], [p_ind], skip=False):
            # if we get timeouts, return what we already have from check_two_state_implication_uncached
            # we need to do this because if this function fails we won't have set tr_trans correctlys
            return tr
        
        pre, post = [p_ind],[p_ind]
        
        print("Trying to augment existing edges")
        for edge_i in reversed(range(max(0, len(self._prior_edges) - 3), len(self._prior_edges))):
            (trans_edge, pre_edge, post_edge) = self._prior_edges[edge_i]
            if check_sat(pre_edge + [p_ind], post_edge + [p_ind]):
                print("Augmented edge")
                pre, post = pre_edge, post_edge
                # remove the edge from prior; it will be added back at the end after it's expanded
                del self._prior_edges[edge_i]
                break
        
        # print("Optimizing post-state")
        # remaining_priors = list(range(p_ind))
        # while len(remaining_priors) > 0:
        #     c = remaining_priors.pop()
        #     if c in post: continue
        #     if check_sat(pre, post+[c]):
        #         post = post + [c]
        
        print("Optimizing edge")  # FOR UNIFORM PRE/POST
        remaining_priors = list(range(p_ind))
        while len(remaining_priors) > 0:
            c = remaining_priors.pop()
            if c in post: continue
            if check_sat(pre + [c], post+[c]):
                post = post + [c]
                pre = pre + [c]
        
        # print("Optimizing pre-state")
        # remaining_priors = list(range(p_ind))
        # while len(remaining_priors) > 0:
        #     c = remaining_priors.pop()
        #     if c in pre: continue
        #     if check_sat(pre + [c], post):
        #         pre = pre + [c]
        assert tr is not None
        pre_size = len(tr[0].as_diagram(0).binder.vs)
        post_size = len(tr[1].as_diagram(0).binder.vs)

        print(f"Done optimizing edge |pre|={len(pre)}, |post|={len(post)}, size pre = {pre_size}, size post = {post_size}")
        self._prior_edges.append((tr_trans, pre, post))
        return tr

def find_generalized_implication(solver: Solver, t: BlockTask, fp: List[Expr], p_ind: int) -> Optional[Tuple[Trace, Trace]]:
    def CI(i: int, j: int) -> bool:
        if (i,j) not in t.ci_cache:
            t.ci_cache[(i,j)] = check_implication(solver, [t.prior_predicates[i]], [t.prior_predicates[j]]) is None
        return t.ci_cache[(i,j)]
    
    p = t.prior_predicates[p_ind]
    tr = check_two_state_implication_uncached(solver, fp + [p], p, minimize=False)
    if tr is None: return None # early out if UNSAT
    # Now try to optimize the edge.
    # predecessor_ps = [i for i in range(len(t.prior_predicates)) if i == p_ind or CI(i, p_ind)]

    # print(f"Toposorting implication predecessors {predecessor_ps}, p_ind={p_ind}")
    # for i in predecessor_ps:
    #     print(f"i={i} {t.prior_predicates[i]}")
    # toposort: List[int] = []
    # while len(predecessor_ps) != 0:
    #     # pick a node with no predecessors
    #     for n in predecessor_ps:
    #         print(f"n={n} {[(j, j == n, CI(j, n)) for j in predecessor_ps]}")
    #         if all(j == n or not CI(j, n) for j in predecessor_ps):
    #             toposort.append(n)
    #             break
    #     else:
    #         print("couldn't find implication-predecessor free state")
    #         toposort.append(predecessor_ps[0])
    #     print(f"Removing {toposort[-1]}")
    #     predecessor_ps = [x for x in predecessor_ps if x != toposort[-1]]
    # assert toposort[-1] == p_ind
    # print("Finding first edge")
    # for prior in toposort:
    #     print(f"Checking for edge {prior} -> ~{p_ind}")
    #     tr = check_two_state_implication_uncached(solver, fp + [t.prior_predicates[prior]], p, minimize=False)
    #     if tr is not None:
    #         return tr
    # assert False

    def check_sat(pre: List[Expr], post: List[Expr]) -> bool: # returns true if satisfiable, and stores transition in `tr`
        nonlocal tr
        tr_prime = check_two_state_implication_uncached(solver, fp + pre, Or(*post), minimize=False, timeout=10000)
        if tr_prime is None:
            return False
        tr = tr_prime
        return True
    
    print("Optimizing post-state")
    pre = [p]
    post = [p]
    remaining_priors = list(t.prior_predicates)
    while len(remaining_priors) > 0:
        c = remaining_priors.pop()
        if check_sat(pre, post+[c]):
            post = post + [c]
    
    print("Optimizing pre-state")
    remaining_priors = list(t.prior_predicates)
    while len(remaining_priors) > 0:
        c = remaining_priors.pop()
        if check_sat(pre + [c], post):
            pre = pre + [c]

    print(f"Done optimizing edge |pre|={len(pre)}, |post|={len(post)}")
    return tr

def fol_ice(solver: Solver) -> None:
    prog = syntax.the_program

    states: List[PDState] = []
    def add_state(s: PDState) -> int:
        i = len(states)
        states.append(s)
        return i


    rest = [inv.expr for inv in prog.invs() if inv.name != 'hard']
    hard = next(inv for inv in prog.invs() if inv.name == 'hard').expr
    pos: List[int] = [] # keep reachable states
    imp: List[Tuple[int, int]] = []

    from set_cover import cover
    start_time = time.time()
    separation_timer = separators.timer.UnlimitedTimer()
    generalization_timer = separators.timer.UnlimitedTimer()
    def print_time() -> None:
        print(f"[time] Elapsed: {time.time()-start_time}, sep: {separation_timer.elapsed()}, gen: {generalization_timer.elapsed()}")
    while True:
        m = check_implication(solver, rest, [hard])
        if m is None:
            print_time()
            print("Eliminated all bad states")
            return
        trace = Trace.from_z3([KEY_ONE], m)
        print(f"The size of the diagram is {len(list(trace.as_diagram().conjuncts()))}, {len(trace.as_diagram().binder.vs)} existentials")
        neg = [add_state((trace, 0))]
        
        # imp = [] # Try resetting edges on each solution
        t = BlockTask(True, neg[0], 0, None, False)

        mp = FOLSeparator(states)
        generalizer = EdgeGeneralizer()
        B = 25
        def CI(i: int, j: int) -> bool:
            if (i,j) not in t.ci_cache:
                t.ci_cache[(i,j)] = check_implication(solver, [t.prior_predicates[i]], [t.prior_predicates[j]]) is None
            return t.ci_cache[(i,j)]

        while True:
            print_time()
            print(f'Separating with |pos|={len(pos)}, |neg|={len(neg)}, |imp|={len(imp)}')
            with separation_timer:
                q = mp.separate(pos=pos, neg=neg, imp=imp, complexity=utils.args.max_complexity)
            if q is None:
                print(f'FOLSeparator returned none')
                return
            print(f'FOLSeparator returned {q}')
            
            p_ind = len(t.prior_predicates)
            t.prior_predicates.append(q)
            res_init = check_initial(solver, q)
            if res_init is not None:
                pos.append(add_state((res_init,0)))
                continue
            
            with generalization_timer:
                res_imp = generalizer.find_generalized_implication(solver, rest, q)
            #res_imp = find_generalized_implication(solver, t, rest, p_ind)
            if res_imp is not None:
                s1, s2 = res_imp
                imp.append((add_state((s1, 0)), add_state((s2, 0))))
                if len(imp) >= B:
                    # Find a set cover of implication constraints that can erase 
                    possiblities = [set(i for i,p in enumerate(t.prior_predicates) if eval_predicate(states[a], p) and not eval_predicate(states[b], p))
                                    for tr_ind, (a,b) in enumerate(imp)]
                    possiblities.append(set(i for i,p in enumerate(t.prior_predicates) if any(not eval_predicate(states[a], p) for a in pos)))
                    covering = cover(possiblities)
                    pre_covering = len(imp)
                    #imp = [imp[i] for i in covering if i < len(imp)]
                    #print(f"Performed set covering bringing implications from {pre_covering} -> {len(imp)}")
                    B = max(B, len(imp) + 5)
                    # for i in range(len(t.prior_predicates)):
                    #     l = []
                    #     for j in range(len(t.prior_predicates)):
                    #         if i < j:
                    #             if CI(i,j):
                    #                 l.append(">")
                    #             elif CI(j,i):
                    #                 l.append("<")
                    #             else:
                    #                 l.append(" ")
                    #         else:
                    #             l.append('.')
                    #     print("".join(l))

                continue

            print(f'Eliminated state with {q}')
            rest.append(q)
            break


def add_argparsers(subparsers: argparse._SubParsersAction) -> Iterable[argparse.ArgumentParser]:

    result : List[argparse.ArgumentParser] = []

    s = subparsers.add_parser('fol-ic3', help='Run IC3 inference with folseparators')
    s.set_defaults(main=fol_ic3)
    s.add_argument('--inductive-generalize', action=utils.YesNoAction, default=True,
                   help='Use inductive generalization when blocking states')
    result.append(s)

    s = subparsers.add_parser('fol-ice', help='Run ICE invariant learning with folseparators')
    s.set_defaults(main=fol_ice)
    result.append(s)

    for s in result:
        s.add_argument('--unroll-to-depth', type=int, help='Unroll transitions to given depth during exploration')
        s.add_argument('--cpus', type=int, help='Number of CPUs to use in parallel')
        s.add_argument('--restarts', action=utils.YesNoAction, default=False, help='Use restarts outside of Z3 by setting Luby timeouts')
        s.add_argument('--induction-width', type=int, default=1, help='Upper bound on weight of dual edges to explore.')
        s.add_argument('--all-subclauses', action=utils.YesNoAction, default=False, help='Add all subclauses of predicates.')
        s.add_argument('--optimize-ctis', action=utils.YesNoAction, default=True, help='Optimize internal ctis')
        
        # FOL specific options
        s.add_argument("--logic", choices=('fol', 'epr', 'universal', 'existential'), default="fol", help="Restrict form of separators to given logic (fol is unrestricted)")
        s.add_argument("--separator", choices=('naive', 'generalized', 'hybrid'), default="hybrid", help="Use the specified separator algorithm")
        s.add_argument("--max-complexity", type=int, default=100, help="Maximum formula complexity")
        s.add_argument("--max-clauses", type=int, default=100, help="Maximum formula matrix clauses")
        s.add_argument("--max-depth", type=int, default=100, help="Maximum formula quantifier depth")
        s.add_argument("--no-dynamic", dest="dynamic", action="store_false", help="Dynamically adjust complexity")
        s.set_defaults(dynamic=True)

    return result