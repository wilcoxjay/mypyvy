'''
This file contains code for the Primal Dual research project
'''
import time
import argparse
import itertools
from itertools import product, chain, combinations, repeat
from collections import defaultdict

from syntax import *
from logic import *
from pd import check_two_state_implication, check_initial

try:
    import separators  # type: ignore # TODO: remove this after we find a way for travis to have folseparators
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
                 pos: Collection[int] = (),
                 neg: Collection[int] = (),
                 imp: Collection[Tuple[int, int]] = (),
    ) -> Optional[Expr]:
        mtimer = separators.timer.UnlimitedTimer()
        timer = separators.timer.UnlimitedTimer()
        with timer:
            f = self.separator.separate(
                pos=[self._state_id(i) for i in pos],
                neg=[self._state_id(i) for i in neg],
                imp=[(self._state_id(i), self._state_id(j)) for i, j in imp],
                max_depth=100,
                max_clauses=100,
                max_complexity=3,
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



def fol_pd_houdini(solver: Solver) -> None:
    induction_width = 1
    prog = syntax.the_program

    # algorithm state
    states: List[PDState] = []
    abstractly_reachable_states: Set[int] = set() # indices into state which are known to be reachable
    transitions: Set[Tuple[int, int]] = set() # known transitions between states

    # all predicates should be true in the initial states
    predicates: List[Expr] = []
    inductive_predicates: Set[int] = set()
    DualTransition = Tuple[FrozenSet[int], FrozenSet[int]]
    dual_transitions: Set[DualTransition] = set()

    def add_state(s: PDState) -> int:
        for i, (t, index) in enumerate(states):
            if t is s[0] and index == s[1]:
                return i
        k = len(states)
        states.append(s)
        return k

    def add_predicate(p: Expr) -> int:
        for i, pred in enumerate(predicates):
            if pred == p:
                return i
        k = len(predicates)
        predicates.append(p)
        return k

    def check_dual_edge(p: List[Expr], q: List[Expr]) -> Optional[Tuple[PDState, PDState]]:
        r = check_two_state_implication(solver, p+q, Implies(And(*p), And(*q)))
        if r is None: return None
        return (r[0],0), (r[1],0)

    def dual_edge(live: Set[int], a: int, induction_width: int) -> Optional[Tuple[List[Expr], List[Expr]]]:
        # find conjunctions p,q such that:
        # - forall l in live. states[l] |= p
        # - p ^ q -> wp(p -> q)
        # - !(states[a] |= q)
        # or return None if no such p,q exist where |q| <= induction_width
        p: List[Expr] = [predicates[i] for i in sorted(inductive_predicates)]
        internal_ctis: Set[Tuple[int, int]] = set() # W, could
        separator = FOLSeparator(states)
        while True:
            q = separator.separate(pos=list(sorted(abstractly_reachable_states)),
                                   neg=[a],
                                   imp=list(sorted(internal_ctis)))
            if q is not None:
                # check for inductiveness
                res = check_initial(solver, q)
                if res is not None:
                    i = add_state((res,0))
                    abstractly_reachable_states.add(i)
                    continue
                res1 = check_dual_edge(p, [q])
                if res1 is not None:
                    (pre, post) = res1
                    a_i, b_i = add_state(pre), add_state(post)
                    internal_ctis.add((a_i, b_i))
                    continue
                # q is inductive relative to p
                return (p,[q])
            else:
                for t in chain(*sorted(internal_ctis)):
                    while True:
                        p_new_conj = separator.separate(
                            pos=list(sorted(abstractly_reachable_states.union(live))),
                            neg=[t]
                        )
                        if p_new_conj is None:
                            # couldn't strengthen p
                            break
                        # check if it satisfied initially
                        res2 = check_initial(solver, p_new_conj)
                        if res2 is not None:
                            i = add_state((res2,0))
                            abstractly_reachable_states.add(i)
                        else:
                            break
                    if p_new_conj is None:
                        continue
                    # strengthen p
                    p.append(p_new_conj)
                    # make sure all CTIs satisfy p in both initial and post state
                    internal_ctis = set(c for c in internal_ctis if eval_predicate(states[c[0]], p_new_conj)\
                                                                    and eval_predicate(states[c[1]], p_new_conj))
                    break
                else:
                    return None

    def primal_houdini(live_predicates: Set[int]) -> Tuple[Set[Tuple[int, int]], Set[int]]:
        # returns ctis, inductive subset of live
        live = set(live_predicates)
        ctis: Set[Tuple[int,int]] = set()
        while True:
            # check if conjunction is inductive.
            assumptions = [predicates[i] for i in sorted(live)]
            for a in sorted(live):
                res = check_two_state_implication(solver, assumptions, predicates[a])
                if res is not None:
                    pre, post = (res[0], 0), (res[1], 0)
                    pre_i = add_state(pre)
                    post_i = add_state(post)
                    ctis.add((pre_i, post_i))
                    live = set(l for l in live if eval_predicate(post, predicates[l]))
                    break
            else:
                # live is inductive
                return (ctis, live)

    def dual_houdini(live_states: Set[int], induction_width: int) -> Tuple[Set[DualTransition], Set[int]]:
        # returns dual cits, subset of "abstractly" reachable states
        live = set(live_states)
        dual_ctis: Set[DualTransition] = set()
        while True:
            for a in sorted(live):
                res = dual_edge(live, a, induction_width)
                if res is not None:
                    (p, q) = res
                    p_i = frozenset(add_predicate(p_conj) for p_conj in p)
                    q_i = frozenset(add_predicate(q_conj) for q_conj in q)
                    dual_ctis.add((p_i, q_i))
                    live = set(l for l in live if all(eval_predicate(states[l], q_conj) for q_conj in q))
                    break
            else:
                # there is no dual edge, so live is all abstractly reachable in the current induction width
                return (dual_ctis, live)

    safety: Set[int] = set()
    for inv in prog.invs():
        if inv.is_safety:
            # Here, could call as_clauses to split apart inv.expr so that we have more fine grained predicates
            safety.add(add_predicate(inv.expr))

    live_predicates: Set[int] = set(safety)
    live_states: Set[int] = set() # states that are "live"
    print([str(predicates[x]) for x in safety])
    while True:
        (ctis, inductive) = primal_houdini(live_predicates)
        inductive_predicates.update(inductive)
        live_states.update(x for cti in ctis for x in cti)
        # filter live_states
        if safety <= inductive_predicates:
            print("safety is inductive!")
            for i in inductive_predicates:
                print(str(predicates[i]))
            break

        (dual_ctis, abstractly_reachable) = dual_houdini(live_states, induction_width)
        abstractly_reachable_states.update(abstractly_reachable)
        live_predicates.update(x for cti in dual_ctis for y in cti for x in y)
        # filter live_predicates
        if not safety <= live_predicates:
            print("found abstractly reachable state(s) violating safety!")
            break

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

class BlockTask(object):
    def __init__(self, is_must: bool, state: int, frame: int, parent: Optional['BlockTask']):
        self.is_must = is_must
        self.state = state
        self.frame = frame
        self.predecessors_eliminated = False
        self.child_count = 0
        self.parent = parent
        if parent is not None:
            parent.child_count += 1
        self.sep: Optional[FOLSeparator] = None
        self.is_unsep = False
        self.imp_constraints: List[Tuple[int, int]] = []
        
    def destroy(self) -> None:
        if self.parent is not None:
            self.parent.child_count -= 1

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
    reachable_states: Set[int] = set()
    states: List[PDState] = []
    transitions: List[Tuple[int,int]] = []
    eval_cache: Dict[Tuple[int,int], bool] = {}

    def add_initial(s: PDState) -> int:
        i = len(states)
        states.append(s)
        initial_states.append(i)
        reachable_states.add(i)
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
    

    tasks: List[BlockTask] = []
    def process_task() -> None:
        nonlocal tasks, system_unsafe
        
        t = next((tt for tt in tasks if tt.child_count == 0), None)
        if t is None:
            print("Couldn't find leaf task")
            return
        
        print(f"Working on {t.state} in frame {t.frame}")
        if not all(eval_pred_state(p_i, t.state) for p_i in frame_predicates_indices(t.frame)):
            print(f"State {t.state} blocked in F_{t.frame}")
            tasks = [x for x in tasks if x is not t]
            t.destroy()
            return
        
        if t.frame == 0 or (t.state in reachable_states):
            # because of the previous if check, we know t.state is an initial state if frame == 0 and reachable otherwise
            if t.is_must:
                print("[IC3] Transition system is UNSAFE!")
                system_unsafe = True
                return
            else:
                reachable_states.add(t.state)
                if t.parent is not None and (t.state, t.parent.state) in transitions:
                    reachable_states.add(t.parent.state)
                print(f"[IC3] Found reachable state {t.state} in F_{t.frame} (now have {len(reachable_states)} reachable states)")
                tasks = [x for x in tasks if x is not t]
                t.destroy()
                return
        
        if not t.predecessors_eliminated:
            s = states[t.state]
            formula_to_block = Not(s[0].as_onestate_formula(s[1])) \
                           if utils.args.logic != "universal" else \
                           Not(s[0].as_diagram(s[1]).to_ast())
            edge = check_two_state_implication(solver, frame_predicates(t.frame-1), formula_to_block)
            if edge is None:
                t.predecessors_eliminated = True
                return
            s_i = add_state((edge[0], 0))
            add_transition(s_i, t.state)
            assert t.frame > 0
            print(f"Eliminating predecessor {s_i} from F_{t.frame - 1}")
            tasks.append(BlockTask(t.is_must, s_i, t.frame - 1, t))
            return
        
        if t.is_unsep:
            path = []
            pt: Optional[BlockTask] = t
            while pt is not None:
                path.append(f"[{'!' if pt.is_must else '?'} F_{pt.frame} s={pt.state}]")
                pt = pt.parent
            remaining = len([i for (i,j) in t.imp_constraints if i not in reachable_states])
            print(f"[IC3] UNSEP {' -> '.join(reversed(path))} remaining={remaining}")
            for (i,j) in t.imp_constraints:
                if i in reachable_states:
                    continue
                if not all(eval_pred_state(p_i, i) for p_i in frame_predicates_indices(t.frame-1)):
                    # one of the constraints has been blocked by a new learned formula. The whole
                    # separation problem could now be satisfiable. Reset the flag on this task
                    t.is_unsep = False
                    t.imp_constraints = []
                    return

                # try to block i
                print(f"Trying to block {i} in F_{t.frame-1}")
                tasks.append(BlockTask(False, i, t.frame-1, t))
                return
            
            # couldn't block any, so this state is reachable
            if t.is_must:
                print("[IC3] Protocol is abstractly UNSAFE!")
                system_unsafe = True
                return
            else:
                # t.state is abstractly reachable. mark it as such
                print("[IC3] Found new (abstractly) reachable state")
                reachable_states.add(t.state)
                return

        if utils.args.inductive_generalize:
            inductive_generalize(t)
        else:
            generalize(t.state, t.frame)

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
            p = sep.separate(pos=pos, neg=[s], imp=[])
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
            tr = check_two_state_implication(solver, frame_predicates(i-1), p)
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

        print(f"Separating in inductive_generalize")
        transitions = list(frame_transitions_indices(t.frame-1))
        p = t.sep.separate(pos=reachable_states, neg=[t.state], imp = transitions)
        if p is None:
            t.is_unsep = True
            # compute unsep core
            remaining, core = transitions[:-1], transitions[-1:]
            while len(remaining) > 0:
                print(f"Checking unsep core {len(remaining)}/{len(transitions)-1}")
                if t.sep.separate(pos=reachable_states, neg=[t.state], imp = core + remaining[:-1]) is not None:
                    core.append(remaining[-1])
                remaining.pop()
            t.imp_constraints = core
            print (f"[IC3] Unsep core is size {len(core)} out of {len(transitions)}")
            return
            
        
        print(f"Candidate predicate is: {p}")
        # init => p?
        state = check_initial(solver, p)
        if state is not None:
            print("Adding new initial state")
            add_initial((state, 0))
            return
        # F_i-1 ^ p => wp(p)?
        tr = check_two_state_implication(solver, frame_predicates(t.frame-1) + [p], p)
        if tr is not None:
            print("Adding new edge")
            s_i, s_j = add_state((tr[0],0)), add_state((tr[1],0))
            add_transition(s_i, s_j)
            return
        
        print_learn_predicate(p)
        idx = add_predicate_to_frame(p, t.frame)
        push()
        return

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
    
    start_time = time.time()
    while not system_unsafe:
        # Try to block things, if there are things to block
        if len(tasks) > 0:
            process_task()
            continue
    
        # Push any predicates that may have just been discovered
        push()
        
        # Check for bad states in the final frame.
        bad_state = check_safe(solver, frame_predicates(frame_n))
        if bad_state is not None:
            s_i = add_state((bad_state, 0))
            tasks.append(BlockTask(True, s_i, frame_n, None))
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
                        print(f"[IC3] invariant {p}")
                    print_summary()
                    return
            print(f"[IC3] Expanding new frame {frame_n+1}")
            push()
            frame_n += 1
    # Loops exits if the protocol is unsafe. Still print statistics
    print_summary()

def fol_ice(solver: Solver) -> None:
    prog = syntax.the_program

    states: List[PDState] = []
    def add_state(s: PDState) -> int:
        i = len(states)
        states.append(s)
        return i

    mp = FOLSeparator(states)
    pos: List[int] = []
    neg: List[int] = []
    imp: List[Tuple[int, int]] = []
    while True:
        q = mp.separate(pos=pos, neg=neg, imp=imp)
        if q is None:
            print(f'FOLSeparator returned none')
            return
        print(f'FOLSeparator returned the following formula:\n{q}')
        res_imp = check_two_state_implication(solver, [q], q)
        if res_imp is not None:
            s1, s2 = res_imp
            imp.append((add_state((s1, 0)), add_state((s2, 0))))
            continue
        res_init = check_initial(solver, q)
        if res_init is not None:
            pos.append(add_state((res_init,0)))
            continue
        res_safe = check_safe(solver, [q])
        if res_safe is not None:
            neg.append(add_state((res_safe, 0)))
            continue
        print(f'Inductive invariant found!')
        break


def add_argparsers(subparsers: argparse._SubParsersAction) -> Iterable[argparse.ArgumentParser]:

    result : List[argparse.ArgumentParser] = []

    s = subparsers.add_parser('fol-pd-houdini', help='Run PD inference with folseparators')
    s.set_defaults(main=fol_pd_houdini)
    result.append(s)

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

    return result