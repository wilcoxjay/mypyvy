'''
This file contains code for the Primal Dual research project
'''
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
    def __init__(self,
                 states: List[PDState],  # assumed to only grow
    ) -> None:
        prog = syntax.the_program
        self.states = states
        self.ids: Dict[int, int] = {}
        # TODO: if mypyvy get's a signature class, update this
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
                timer=timer
            )
        if f is None:
            
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

def fol_ic3(solver: Solver) -> None:
    prog = syntax.the_program

    predicates: List[Expr] = []
    frame_numbers: List[int] = [] # for each predicate, what is the highest frame?
    frame_n: int = 1 # highest frame

    def frame_predicates(i: int) -> List[Expr]:
        return [p for p,f in zip(predicates, frame_numbers) if i <= f]
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
    states: List[PDState] = []
    free_states: List[int] = []
    transitions: List[Tuple[int,int]] = []
    eval_cache: Dict[Tuple[int,int], bool] = {}

    def add_initial(s: PDState) -> int:
        i = len(states)
        states.append(s)
        initial_states.append(i)
        return i
    def add_state(s: PDState, frame: int) -> int:
        i = len(states)
        states.append(s)
        free_states.append(i)
        return i       
    def add_transition(pre: PDState, post: PDState, frame: int) -> Tuple[int, int]:
        i = len(states)
        states.append(pre)
        j = len(states)
        states.append(post)
        transitions.append((i,j))
        return (i,j)
    def eval_pred_state(pred_idx: int, state_idx: int) -> bool:
        if (pred_idx, state_idx) not in eval_cache:
            eval_cache[(pred_idx, state_idx)] = eval_predicate(states[state_idx], predicates[pred_idx])
        return eval_cache[(pred_idx, state_idx)]
        
    def frame_states(frame:int) -> Sequence[PDState]:
        pred_indices = [i for i,f in enumerate(frame_numbers) if frame <= f]
        return [s for i,s in enumerate(states) if all(eval_pred_state(p, i) for p in pred_indices)]

    def frame_transitions(frame:int) -> Sequence[Tuple[PDState, PDState]]:
        pred_indices = [i for i,f in enumerate(frame_numbers) if frame <= f]
        return [(states[a], states[b]) for a,b in transitions if all(eval_pred_state(p, a) for p in pred_indices)]

    def block(s: PDState, i: int) -> None:
        print(f"blocking state in {i}")
        if i == 0:
            raise RuntimeError("Protocol is UNSAFE!") # this should exit more cleanly
        # block all predecesors
        formula_to_block = Not(s[0].as_onestate_formula(s[1])) \
                           if utils.args.logic != "universal" else \
                           Not(s[0].as_diagram(s[1]).to_ast())
        while True:
            edge = check_two_state_implication(solver, frame_predicates(i-1), formula_to_block)
            if edge is None:
                break
            (pre, post) = edge
            print ("Pre\n",pre)
            print ("Post\n",post)
            block((pre, 0), i-1)
            # check if s has been eliminated by a learned and pushed formula in a recursive block()
            if not all(eval_predicate(s, p) for p in frame_predicates(i)):
                print(f"State blocked by pushed predicate, would have been in frame {i}")
                return # s is already blocked
        if utils.args.inductive_generalize:
            inductive_generalize(s, i)
        else:
            generalize(s, i)

    def generalize(s: PDState, i: int) -> None:
        print("Generalizing")
        # find p s.t. p is negative on s, init => p, F_i-1 => p, and F_i-1 => wp(p)
        separation_states: List[PDState] = [s]
        pos: Set[int] = set()
        for st in frame_states(i-1):
            pos.add(len(separation_states))
            separation_states.append(st)
        for (pre, post) in frame_transitions(i-1):
            pos.add(len(separation_states))
            separation_states.append(pre)
            pos.add(len(separation_states))
            separation_states.append(post)

        sep = FOLSeparator(separation_states)

        while True:
            print("Separating")
            p = sep.separate(pos=pos, neg=[0], imp=[])
            if p is None: raise RuntimeError("couldn't separate in generalize()")
            print(f"Candidate predicate is: {p}")

            # F_0 => p?
            print("check initial")
            state = check_initial(solver, p)
            if state is not None:
                print("Adding new initial state")
                pos.add(len(separation_states))
                separation_states.append((state, 0))
                add_initial((state, 0))
                continue
            # F_i-1 => p?
            print("check implication")
            cex = check_implication(solver, frame_predicates(i-1), [p])
            if cex is not None:
                print("Adding new free pre-state")
                pos.add(len(separation_states))
                t = Trace.from_z3([KEY_ONE], cex)
                separation_states.append((t,0))
                add_state((t,0), i)
                continue

            # F_i-1 => wp(p)?
            tr = check_two_state_implication(solver, frame_predicates(i-1), p)
            if tr is not None:
                (pre_st, post_st) = tr
                print("Adding new edge")
                pos.add(len(separation_states))
                separation_states.append((pre_st,0))
                pos.add(len(separation_states))
                separation_states.append((post_st,0))
                add_transition((pre_st,0), (post_st,0), i)
                continue


            print(f"Learned new predicate: {p}")
            idx = add_predicate_to_frame(p, i)
            push()
            return
    
    def inductive_generalize(s: PDState, i: int) -> None:
        print("Inductive generalizing")
        # find p s.t. p is negative on s, init => p, F_i-1 ^ p => wp(p)
        separation_states: List[PDState] = [s]
        pos: Set[int] = set()
        imp: Set[Tuple[int,int]] = set()
        for st_idx in initial_states:
            pos.add(len(separation_states))
            separation_states.append(states[st_idx])
        for (pre, post) in frame_transitions(i-1):
            imp.add((len(separation_states), len(separation_states)+1))
            separation_states.append(pre)
            separation_states.append(post)

        sep = FOLSeparator(separation_states)

        while True:
            print("Separating")
            p = sep.separate(pos=pos, neg=[0], imp=imp)
            if p is None: raise RuntimeError("couldn't separate in inductive_generalize()")
            print(f"Candidate predicate is: {p}")

            # init => p?
            print("check initial")
            state = check_initial(solver, p)
            if state is not None:
                print("Adding new initial state")
                pos.add(len(separation_states))
                separation_states.append((state, 0))
                add_initial((state, 0))
                continue
            # F_i-1 ^ p => wp(p)?
            tr = check_two_state_implication(solver, frame_predicates(i-1) + [p], p)
            if tr is not None:
                (pre_st, post_st) = tr
                print("Adding new edge")
                imp.add((len(separation_states), len(separation_states)+1))
                separation_states.append((pre_st,0))
                separation_states.append((post_st,0))
                add_transition((pre_st,0), (post_st,0), i)
                continue

            print(f"Learned new predicate: {p}")
            idx = add_predicate_to_frame(p, i)
            push()
            return
    def push() -> None:
        for frame in range(frame_n):
            for i in range(len(frame_numbers)):
                if frame_numbers[i] == frame:
                    # try to push i
                    cex = check_two_state_implication(solver, frame_predicates(frame), predicates[i])
                    if cex is None:
                        frame_numbers[i] += 1
                        print(f"pushed {predicates[i]} to frame {frame_numbers[i]}")

    def print_predicates() -> None:
        print ("predicate ----")
        for f,p in sorted(zip(frame_numbers, predicates), key = lambda x: x[0]):
            print(f"predicate {f} {p}")

    for init_decl in prog.inits():
        predicates.append(init_decl.expr)
        frame_numbers.append(0)

    while True:
        push()
        bad_state = check_safe(solver, frame_predicates(frame_n))
        if bad_state is not None:
            block((bad_state, 0), frame_n)
        else:
            print_predicates()
            print("Checking for an inductive frame")
            for inv_frame in reversed(range(1,frame_n + 1)):
                # skip frames identical to a previous one
                if not any(inv_frame == f for f in frame_numbers):
                    continue
                ps = frame_predicates(inv_frame)
                if all(check_two_state_implication(solver, ps, p) is None for p in ps):
                    print(f"Found inductive invariant in frame {inv_frame}!")
                    for p in ps:
                        print(f"invariant {p}")
                    return
            print(f"Expanding new frame {frame_n+1}")
            frame_n += 1

def fol_ice(solver: Solver) -> None:
    prog = syntax.the_program
    # invs = list(chain(*(as_clauses(inv.expr) for inv in prog.invs())))
    #print('Trying to FOL-ICE learn the following invariant:')
    #for p in sorted(invs, key=lambda x: len(str(x))):
    #    print(p)
    #print('='*80)

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
        s.add_argument('--all-subclauses',  action=utils.YesNoAction, default=False, help='Add all subclauses of predicates.')
        s.add_argument('--optimize-ctis',  action=utils.YesNoAction, default=True, help='Optimize internal ctis')
        
        # FOL specific options
        s.add_argument("--logic", choices=('fol', 'epr', 'universal', 'existential'), default="fol", help="Restrict form of separators to given logic (fol is unrestricted)")
        s.add_argument("--separator", choices=('naive', 'generalized', 'hybrid'), default="hybrid", help="Use the specified separator algorithm")

    return result