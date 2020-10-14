
import argparse
import multiprocessing
import random
from threading import local
import time
from multiprocessing import Process, Manager
from multiprocessing.connection import Connection
from typing import AnyStr, IO, NamedTuple, TextIO
from separators.logic import symbols

from syntax import *
from logic import *
from fol_trans import *

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

# Returns a trace where index 0 = pre-state, 1 = post-state
def two_state_trace_from_z3(m: z3.ModelRef) -> Trace:
    return Trace.from_z3([KEY_OLD, KEY_NEW], m)

def check_two_state_implication_uncached(solver: Solver, ps: List[Expr], c: Expr, minimize: Optional[bool] = None, timeout: int = 0) -> Optional[Trace]:
    edge = check_two_state_implication_all_transitions_unknown_is_unsat(solver, old_hyps = ps, new_conc = c, minimize=minimize, timeout=timeout)
    return two_state_trace_from_z3(edge[0]) if edge is not None else None

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
        self.generalizer: Optional[EdgeGeneralizer] = None
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

class WorkerArgs(NamedTuple):
    name: str
    logic: str
    expt_flags: Set[str]
    blocked_symbols: List[str]
class Constraint(object):
    pass
class PositiveStruct(Constraint):
    def __init__(self, s: int):
        self.s = s
class NegativeStruct(Constraint):
    def __init__(self, s: int):
        self.s = s
class ImplicationStructs(Constraint):
    def __init__(self, s: int, t: int):
        self.s = s
        self.t = t

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
            s_i = add_state((edge, 0))
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

        if 'parallelism' in utils.args.expt_flags:
            inductive_generalize_parallel(t)
        elif utils.args.inductive_generalize:
            ii = inductive_generalize(t)
            if ii is not None:
                push()
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
                s_i, s_j = add_state((tr,0)), add_state((tr,1))
                add_transition(s_i, s_j)
                continue

            print_learn_predicate(p)
            idx = add_predicate_to_frame(p, i)
            push()
            return

    def inductive_generalize(t: BlockTask) -> Optional[int]:
        # find p s.t. p is negative on s, init => p, F_i-1 ^ p => wp(p)
        print("Inductive generalizing")
        if t.sep is None:
            t.sep = FOLSeparator(states)
            # Note, we may want to seed this set with some subset of the known frame transitions
            # which are most likely to constrain the solution, while avoiding adding all constraints
            # if there are very many of them.
            t.imp_constraints = []

        all_transitions = list(frame_transitions_indices(t.frame-1))
        # First, filter out elements of t.imp_constraints that are no longer active.
        t.imp_constraints = [x for x in t.imp_constraints if x in all_transitions]

        abs_reach = abstractly_reachable()

        p = t.sep.separate(pos=abs_reach, neg=[t.state], imp = t.imp_constraints, complexity=K_bound)
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
            return None
        
        p_respects_all_transitions = True
        for (s_i, s_j) in reversed(all_transitions): # try most recent first
            if (s_i, s_j) in t.imp_constraints:
                continue
            if eval_predicate(states[s_i], p) and not eval_predicate(states[s_j], p):
                p_respects_all_transitions = False
                t.imp_constraints.append((s_i, s_j))
                # print_constraint_matrix(t)
                # simplify_constraints(t, all_transitions, set(abs_reach))
                break # only add up to one transition at a time
        if not p_respects_all_transitions:
            # exit and go back up to the top of this function, but with new constraints
            print("Added cached transition to constraints")
            return None
        
        print(f"Candidate predicate is: {p}")
        p_ind = len(t.prior_predicates)
        t.prior_predicates.append(p)
        t.prior_eval_cache.append((set(), set()))

        # init => p?
        state = check_initial(solver, p)
        if state is not None:
            print("Adding new initial state")
            general = generalize_initial(solver, (state, 0))
            print("Initial generalized model:")
            print(general)

            add_initial((state, 0))
            return None
        # F_i-1 ^ p => wp(p)?
        
        if t.generalizer is None:
            t.generalizer = TrivialEdgeGeneralizer()
        res = t.generalizer.find_generalized_implication(solver, states[t.state], frame_predicates(t.frame-1), p)
        if res is not None:
            print("Adding new edge")
            tr, trans = res

            if False:
                two_state_model = generalize_cti(solver, trans, tr, frame_predicates(t.frame-1))
                print("CTI generalized model:")
                print(two_state_model)

            s_i, s_j = add_state((tr,0)), add_state((tr,1))
            add_transition(s_i, s_j)
            t.imp_constraints.append((s_i, s_j))
            return None
        
        print_learn_predicate(p)
        idx = add_predicate_to_frame(p, t.frame)
        return idx
    class Logger(object):
        def __init__(self, out: TextIO, name: str):
            self._out = out
            self.encoding = out.encoding
            self._name = name
        def write(self, s: str) -> None:
            if s.startswith("Candidate"):
                self._out.write(f"[{self._name}] {s}\n")
                self._out.flush()
    def sig_symbols(s: separators.logic.Signature) -> List[str]:
        r: List[str] = []
        r.extend(s.relations.keys())
        r.extend(s.functions.keys())
        r.extend(s.constants.keys())
        return r

    

    def separation_worker(args: WorkerArgs, pipe: Connection) -> None:
        sig = prog_to_sig(syntax.the_program, two_state=False)
        true_stdout = sys.stdout
        sys.stdout = Logger(true_stdout, args.name) # type: ignore
        nonlocal K_bound
        K_bound = 1000
        if 'impmatrix' in args.expt_flags:
            backing_sep: separators.separate.Separator = separators.separate.ImplicationSeparator(sig, logic = args.logic, expt_flags= args.expt_flags, blocked_symbols=args.blocked_symbols)
        else:
            backing_sep = separators.separate.HybridSeparator(sig, logic = args.logic, expt_flags= args.expt_flags, blocked_symbols=args.blocked_symbols)
        local_states: List[PDState] = []
        constraints: List[Constraint] = []
        sep = FOLSeparator(local_states, backing_sep)
        print("Starting worker")
        while True:
            req = pipe.recv()
            if isinstance(req, Constraint):
                constraints.append(req)
            elif req is None:
                print("Separating")
                p = sep.separate(pos = [c.s for c in constraints if isinstance(c, PositiveStruct)],
                                 neg = [c.s for c in constraints if isinstance(c, NegativeStruct)],
                                 imp = [(c.s, c.t) for c in constraints if isinstance(c, ImplicationStructs)], complexity=K_bound)
                if p is not None:
                    pipe.send((args.name, p))
                else:
                    print(f"[error] Separator could not separate in {args.name}", file=sys.stderr)
            elif isinstance(req, tuple):
                while len(local_states) < req[0] + 1:
                    local_states.append(req[1])
                local_states[req[0]] = req[1]
            else:
                assert False
                
    class WorkerHandle(object):
        def __init__(self, name: str, proc: Process, conn: Connection):
            self.name = name
            self.proc = proc
            self.conn = conn
            self.states_seen: int = 0
            self.constraints_seen: int = 0
            
        def fileno(self) -> int:
            return self.conn.fileno()

    def inductive_generalize_parallel(t: BlockTask) -> None:
        sig = prog_to_sig(syntax.the_program, two_state=False)
        # find p s.t. p is negative on s, init => p, F_i-1 ^ p => wp(p)
        # def inductive_generalize_worker(name, logic: str, expt_flags: Set[str], blocked_symbols: List[str] = []) -> None:
        #     true_stdout = sys.stdout
        #     sys.stdout = Logger(true_stdout, name)
        #     nonlocal K_bound
        #     K_bound = 1000
        #     if 'impmatrix' in expt_flags:
        #         backing_sep = separators.separate.ImplicationSeparator(sig, logic = logic, expt_flags= expt_flags, blocked_symbols=blocked_symbols)
        #     else:
        #         backing_sep = separators.separate.HybridSeparator(sig, logic = logic, expt_flags= expt_flags, blocked_symbols=blocked_symbols)
        #     t.sep = FOLSeparator(states, backing_sep)
        #     while True:
        #         i = inductive_generalize(t)
        #         if i is not None:
        #             success_queue.put((name, predicates[i]))

        golden: List[separators.logic.Formula] = []
        for inv in syntax.the_program.invs():
            if states[t.state][0].as_state(states[t.state][1]).eval(inv.expr) == False:
                cex = check_two_state_implication_all_transitions(solver, frame_predicates(t.frame-1), inv.expr, minimize=False)
                g_as_formula = predicate_to_formula(inv.expr)
                golden.append(g_as_formula)
                print("Possible formula is:", g_as_formula, '(relatively inductive)' if cex is None else '(not relatively inductive)')
        
        success_queue: multiprocessing.Queue[Tuple[str, Expr]] = multiprocessing.Queue()
        print("Starting parallel inductive_generalize...")
        workers: List[WorkerHandle] = []
        def L(a: WorkerArgs) -> None:
            (main, worker) = multiprocessing.Pipe(duplex = True)
            p = Process(target=separation_worker, args = (a, worker))
            workers.append(WorkerHandle(a.name, p, main))
            p.start()


        all_syms = sig_symbols(sig)
        for g in []: #all_syms: #golden:
            #syms = symbols(g)
            #blocked_symbols = list(set(all_syms) - set(syms))
            blocked_symbols = [g]
            if utils.args.logic == 'universal':
                pass
            if utils.args.logic == 'fol':
                L(WorkerArgs('full-b', 'fol', set(), blocked_symbols))
                L(WorkerArgs('alt1-b', 'fol', set(['alternation1']), blocked_symbols))
                L(WorkerArgs('m4-b', 'fol', set(['matrixsize4']), blocked_symbols))
                # L(WorkerArgs('imp', 'fol', set(['impmatrix']), blocked_symbols))
            
            L(WorkerArgs('Afull-b', 'universal', set(), blocked_symbols))
            L(WorkerArgs('Am4-b', 'universal', set(['matrixsize4']), blocked_symbols))
        
        if utils.args.logic == 'fol':
            L(WorkerArgs('full', 'fol', set(), []))
            L(WorkerArgs('alt1', 'fol', set(['alternation1']), []))
            L(WorkerArgs('m4', 'fol', set(['matrixsize4']), []))
            # L(WorkerArgs('imp', 'fol', set(['impmatrix']), blocked_symbols))
        
        L(WorkerArgs('Afull', 'universal', set(), []))
        L(WorkerArgs('Am4', 'universal', set(['matrixsize4']), []))
        L(WorkerArgs('Am4', 'universal', set(['matrixsize2']), []))

        local_states: List[PDState] = [states[t.state]]
        constraints: List[Constraint] = [NegativeStruct(0)]

        def update_worker(w: WorkerHandle) -> None:
            '''Send the latest state and constraints to the workers'''
            while w.states_seen < len(local_states):
                w.conn.send((w.states_seen, local_states[w.states_seen]))
                w.states_seen += 1
            while w.constraints_seen < len(constraints):
                w.conn.send(constraints[w.constraints_seen])
                w.constraints_seen += 1

        def is_solution(p: Expr) -> bool:
            pass
            # First check the current constraints, and see if p respects all of those:
            for c in constraints:
                if isinstance(c, PositiveStruct):
                    if not eval_predicate(local_states[c.s], p):
                        return False
                elif isinstance(c, NegativeStruct):
                    if eval_predicate(local_states[c.s], p):
                        assert False and "candidates should always respect the negative constraint"
                        return False
                elif isinstance(c, ImplicationStructs):
                    if eval_predicate(local_states[c.s], p) and not eval_predicate(local_states[c.t], p):
                        return False

            # The predicate satisfies all existing constraints. Now check for real.
            state = check_initial(solver, p)
            if state is not None:
                print("Adding new initial state")
                s = len(local_states)
                local_states.append((state, 0))
                constraints.append(PositiveStruct(s))
                return False
            
            # F_i-1 ^ p => wp(p)?
            gen = TrivialEdgeGeneralizer()
            res = gen.find_generalized_implication(solver, states[t.state], frame_predicates(t.frame-1), p)
            if res is not None:
                print("Adding new edge")
                tr, trans = res
                s = len(local_states)
                local_states.append((tr,0))
                tt = len(local_states)
                local_states.append((tr,1))
                constraints.append(ImplicationStructs(s,tt))
                return False

            # If we get here, then p is a solution to our inductive generalization query        
            return True
        
        for w in workers:
            update_worker(w)
            w.conn.send(None) # start them all working
        print(f"Started initial workers (x{len(workers)})")
        while True:
            ready = multiprocessing.connection.wait([w.conn for w in workers])
            for r in ready:
                for w in workers:
                    if w.conn is r:
                        worker = w
                        break
                else:
                    assert False
                (_, p) = worker.conn.recv()
                print(f"[IC3] Candidate: {p}")
                assert isinstance(p, Expr)
                if is_solution(p):
                    print(f"Accepting predicate from {worker.name}")
                    for w in workers:
                        w.proc.kill()
                    
                    print_learn_predicate(p)
                    add_predicate_to_frame(p, t.frame)
                    print("Finished parallel inductive_generalize.")
                    push()
                    return
                update_worker(worker)
                worker.conn.send(None)
        
    def push() -> None:
        made_changes = False
        for frame in range(frame_n):
            for i in range(len(frame_numbers)):
                if frame_numbers[i] == frame:
                    # try to push i
                    cex = check_two_state_implication_all_transitions(solver, frame_predicates(frame), predicates[i], minimize=False)
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
    for safety_decl in prog.safeties():
        predicates.append(safety_decl.expr)
        frame_numbers.append(0)
    for inv_decl in prog.invs():
        if 'free-lemma' in utils.args.expt_flags and inv_decl.name == 'free_lemma':
            predicates.append(inv_decl.expr)
            frame_numbers.append(0)
        
    K_limit = utils.args.max_complexity
    K_bound = 1 if utils.args.dynamic else K_limit
    print(f"[IC3] Inferring with K_bound = {K_bound} up to {K_limit} ({'dynamic' if utils.args.dynamic else 'static'}), with max clauses={utils.args.max_clauses}, depth={utils.args.max_depth}")
    start_time = time.time()
    while not system_unsafe:
        print(f"[time] Elapsed: {time.time()-start_time:0.3f}")
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
                if all(check_two_state_implication_all_transitions(solver, ps, p, minimize=False) is None for p in ps):
                    
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
    '''Abstract base class for methods that find generalized CTIs (i.e. counterexample edges) to And(fp) => wp(p).'''
    def find_generalized_implication(self, solver: Solver, state: PDState, fp: List[Expr], p: Expr) -> Optional[Tuple[Trace, DefinitionDecl]]: pass

class TrivialEdgeGeneralizer(EdgeGeneralizer):
    '''Generates edges as the first thing that comes from the solver without actually generalizing.'''
    def __init__(self) -> None:
        pass
    def find_generalized_implication(self, solver: Solver, state: PDState, fp: List[Expr], p: Expr) -> Optional[Tuple[Trace, DefinitionDecl]]:
        for trans in syntax.the_program.transitions():
            res, tr = check_two_state_implication_generalized(solver, trans, fp + [p], p, minimize=False, timeout=10000)
            if tr is not None:
                return two_state_trace_from_z3(tr), trans
        return None

class LatticeEdgeGeneralizer(EdgeGeneralizer):
    '''Generalizes edges by climbing the lattice of implications.'''
    def __init__(self) -> None:
        self.sig = prog_to_sig(syntax.the_program)
    def find_generalized_implication(self, solver: Solver, state: PDState, fp: List[Expr], p: Expr) -> Optional[Tuple[Trace, DefinitionDecl]]:
        result: Optional[Tuple[int, Trace, DefinitionDecl]] = None
        
        N = 5 if 'repeatlattice5' in utils.args.expt_flags else 2 if 'repeatlattice2' in utils.args.expt_flags else 1
        for rep in range(N):
            r = self._lattice_climb(solver, state, fp, p)
            if result is None:
                result = r
            elif r is None:
                pass
            elif r[0] > result[0]:
                result = r
        
        if result is not None:
            print(f"Final lattice distance is {result[0]}")
            return result[1], result[2]
        return None
    def _lattice_climb(self, solver: Solver, state: PDState, fp: List[Expr], p: Expr) -> Optional[Tuple[int, Trace, DefinitionDecl]]:
        tr = check_two_state_implication_uncached(solver, fp + [p], p, minimize=False)
        if tr is None: return None # early out if UNSAT
        
        all_transitions = []
        tr_trans = next(syntax.the_program.transitions())
        for trans in syntax.the_program.transitions():
            res, tr_prime = check_two_state_implication_generalized(solver, trans, fp + [p], p, minimize=False, timeout=10000)
            if res == z3.sat:
                assert tr_prime is not None
                all_transitions.append(trans)
                tr = two_state_trace_from_z3(tr_prime)
                tr_trans = trans
                        
        def check_sat(a: Expr, b: Expr) -> bool: # returns true if satisfiable, and stores transition in `tr` and `tr_trans`
            nonlocal tr, tr_trans
            for trans in all_transitions:
                res, tr_prime = check_two_state_implication_generalized(solver, trans, fp + [a], b, minimize=False, timeout=10000)
                if tr_prime is None:
                    continue
                tr = two_state_trace_from_z3(tr_prime)
                tr_trans = trans
                return True
            return False
        print("Optimizing post-state")
        pre = p
        post = p
        pre_dist, post_dist = 0,0
        while True:
            x = [formula_to_predicate(x) for x in separators.separate.successor_formula(self.sig, predicate_to_formula(post))]
            random.shuffle(x)
            for next_p in x:
                if eval_predicate(state, next_p): # TODO: should this be eval next_p or not eval next_p or eval post?
                    continue
                if check_sat(pre, next_p):
                    post = next_p
                    post_dist += 1
                    break
            else:
                break
        print("Optimizing pre-state")
        while True:
            x = [formula_to_predicate(x) for x in separators.separate.predecessor_formula(self.sig, predicate_to_formula(pre))]
            random.shuffle(x)
            for next_p in x:
                if check_sat(next_p, post):
                    pre = next_p
                    pre_dist += 1
                    break
            else:
                break
        print(f"Found edge between predicates {pre} --> {post}")
        print(f"Done optimizing edge, lattice distance is {post_dist + pre_dist} (post {post_dist}, pre {pre_dist})")
        return post_dist + pre_dist, tr, tr_trans

class CombiningEdgeGeneralizer(EdgeGeneralizer):
    '''Generalizes edges by combining them into one query. Not recommended.'''
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
    
    def find_generalized_implication(self, solver: Solver, state: PDState, fp: List[Expr], p: Expr) -> Optional[Tuple[Trace, DefinitionDecl]]:
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
                    tr = two_state_trace_from_z3(tr_prime)
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
            return tr, tr_trans
        
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

        print("Optimizing edge")
        remaining_priors = list(range(p_ind))
        while len(remaining_priors) > 0:
            c = remaining_priors.pop()
            if c in post: continue
            if check_sat(pre + [c], post+[c]):
                post = post + [c]
                pre = pre + [c]
        
        assert tr is not None
        pre_size = len(tr.as_diagram(0).binder.vs)
        post_size = len(tr.as_diagram(1).binder.vs)

        print(f"Done optimizing edge |pre|={len(pre)}, |post|={len(post)}, size pre = {pre_size}, size post = {post_size}")
        self._prior_edges.append((tr_trans, pre, post))
        return tr, tr_trans

def generalize_initial(solver: Solver, m: PDState) -> separators.logic.Model:
    prog = syntax.the_program
    M: separators.logic.Model = state_to_model(m)

    inits = tuple(init.expr for init in prog.inits())
    axioms = tuple(init.expr for init in prog.axioms())
    derived_axioms = tuple(r.derived_axiom for r in prog.derived_relations() if r.derived_axiom is not None)
    e = separators.logic.And([*(predicate_to_formula(i) for i in inits), 
                              *(predicate_to_formula(a) for a in axioms),
                              *(predicate_to_formula(a) for a in derived_axioms)])
    return separators.learn.generalize_model(M, e, label='Initial')

def generalize_cti(solver: Solver, trans: DefinitionDecl, tr: Trace, frame: Sequence[Expr]) -> separators.logic.Model:
    prog = syntax.the_program
    M: separators.logic.Model = two_state_trace_to_model(tr, two_state=True)
    axioms = tuple(init.expr for init in prog.axioms())
    derived_axioms = tuple(r.derived_axiom for r in prog.derived_relations() if r.derived_axiom is not None)
    e = separators.logic.And([*(predicate_to_formula(a) for a in axioms),
                              *(predicate_to_formula(a) for a in derived_axioms), # ensure axioms for pre-state
                              *(predicate_to_formula(a, two_state=True) for a in derived_axioms), # ensure axioms for post-state
                              transition_to_formula(trans),
                              *(predicate_to_formula(f) for f in frame)])
    # print(trans)
    # for c in transition_to_formula(trans).c:
    #     print(c, '=', separators.check.check(c, M))
    # assert separators.check.check(transition_to_formula(trans), M)
    return separators.learn.generalize_model(M, e, two_state=True, label='CTI')

def fol_ice(solver: Solver) -> None:
    
    states: List[PDState] = []
    def add_state(s: PDState) -> int:
        i = len(states)
        states.append(s)
        return i

    rest = [inv.expr for inv in syntax.the_program.invs() if inv.name != 'hard']
    hard = next(inv for inv in syntax.the_program.invs() if inv.name == 'hard').expr
    pos: List[int] = [] # keep reachable states
    imp: List[Tuple[int, int]] = []
    mp = FOLSeparator(states)

    start_time = time.time()
    separation_timer = separators.timer.UnlimitedTimer()
    generalization_timer = separators.timer.UnlimitedTimer()
    def print_time() -> None:
        print(f"[time] Elapsed: {time.time()-start_time:0.3f}, sep: {separation_timer.elapsed():0.3f}, gen: {generalization_timer.elapsed():0.3f}")

    print(f'Looking for golden formula {hard}')
    print(f'Experimental flags: {", ".join(utils.args.expt_flags)}')
    while True:
        m = check_implication(solver, rest, [hard])
        if m is None:
            print_time()
            print("[ICE] Eliminated all bad states")
            return
        trace = Trace.from_z3([KEY_ONE], m)
        print(f"The size of the diagram is {len(list(trace.as_diagram().conjuncts()))}, with {len(trace.as_diagram().binder.vs)} existentials")
        neg = [add_state((trace, 0))]
        generalizer = LatticeEdgeGeneralizer()
        
        #imp = [] # Try resetting edges on each solution
        #mp = FOLSeparator(states) # Try resetting separator
        
        while True:
            print_time()
            print(f'Separating with |pos|={len(pos)}, |neg|={len(neg)}, |imp|={len(imp)}')
            with separation_timer:
                q = mp.separate(pos=pos, neg=neg, imp=imp, complexity=utils.args.max_complexity)
            if q is None:
                print(f'FOLSeparator returned none')
                return
            print(f'FOLSeparator returned {q}')
            
            res_init = check_initial(solver, q)
            if res_init is not None:
                M_general = generalize_initial(solver, (res_init, 0))
                print("Initial state generalized model:")
                print(M_general)
                if 'eagerinitial' in utils.args.expt_flags:
                    for completion in separators.learn.expand_completions(M_general):
                        print('Adding completion', completion)
                        pos.append(add_state(model_to_state(completion)))
                else:
                    pos.append(add_state((res_init,0)))                
                continue
            
            with generalization_timer:
                res = generalizer.find_generalized_implication(solver, states[neg[0]], rest, q)
            if res is None:
                print(f'[ICE] Eliminated state with {q}')
                rest.append(q)
                break
            
            tr, trans = res
            two_state_model = generalize_cti(solver, trans, tr, rest)
            print("CTI generalized model:")
            print(two_state_model)
            # pre = separators.learn.two_state_pre(two_state_model)
            # print("Pre-state projection:\n{pre}")
            # post = separators.learn.two_state_post(two_state_model)
            # print("Post-state projection:\n{post}")
            # print(f"Generalized CTI to {len(list(separators.learn.expand_completions(pre)))} pre and {len(list(separators.learn.expand_completions(post)))} post")
            
            if 'eagercti' in utils.args.expt_flags:
                print("Expanding a CTI")
                raise NotImplemented
            else:
                st1, st2 = add_state((tr, 0)), add_state((tr, 1))
                if 'goldenimptopos' in utils.args.expt_flags and eval_predicate(states[st1], hard):
                    print("Golden formula was true for pre-state; adding positive constraint")
                    pos.extend([st1, st2])
                else:
                    imp.append((st1, st2))

def fol_extract(solver: Solver) -> None:
    import os.path
    prog = syntax.the_program
    sig = prog_to_sig(prog)
    names: Set[str] = set()
    next = 0
    def generate() -> str:
        nonlocal next, names
        n = f"c{next}"
        next += 1
        if n in names:
            return generate()
        else:
            return n
    for x in prog.invs():
        name = x.name if x.name is not None else generate()
        with open(f"out/extracts/{os.path.splitext(os.path.basename(utils.args.filename))[0]}-{name}.fol", "w") as f:
                
            f.write("; File: " + utils.args.filename + "\n")
            f.write("; Original: " + " ".join(str(x).split("\n")) + "\n")
            f.write(str(sig))
            f.write("; End sig\n\n; Axioms\n")
            for ax in prog.axioms():
                f.write(f"(axiom {repr(predicate_to_formula(ax.expr))})\n")
            f.write(f"\n; Conjecture {name}\n")
            f.write(f"(conjecture {repr(predicate_to_formula(x.expr))})\n")
        names.add(name)


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

    s = subparsers.add_parser('fol-extract', help='Extract conjuncts to a file')
    s.set_defaults(main=fol_extract)
    result.append(s)

    for s in result:
       
        # FOL specific options
        s.add_argument("--logic", choices=('fol', 'epr', 'universal', 'existential'), default="fol", help="Restrict form of separators to given logic (fol is unrestricted)")
        s.add_argument("--separator", choices=('naive', 'generalized', 'hybrid'), default="hybrid", help="Use the specified separator algorithm")
        s.add_argument("--max-complexity", type=int, default=100, help="Maximum formula complexity")
        s.add_argument("--max-clauses", type=int, default=100, help="Maximum formula matrix clauses")
        s.add_argument("--max-depth", type=int, default=100, help="Maximum formula quantifier depth")
        s.add_argument("--dynamic", dest="dynamic", default=False, action="store_true", help="Dynamically adjust complexity")
        s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: set(x.split(',')), default=set(), help="Experimental flags")

    return result