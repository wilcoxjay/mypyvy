
import argparse
from asyncio.exceptions import CancelledError
import multiprocessing
from operator import truediv
import os.path
import random
import time
from multiprocessing import Process
from multiprocessing.connection import Connection
from typing import Awaitable, DefaultDict, NamedTuple, TextIO
import asyncio
from separators.separate import HybridSeparator, ImplicationSeparator, Separator
from separators.timer import UnlimitedTimer

from syntax import *
from logic import *
from fol_trans import *

def initial_conditions() -> List[Expr]:
    prog = syntax.the_program
    return [init.expr for init in prog.inits()]
    
def check_initial(solver: Solver, p: Expr, minimize: Optional[bool] = None) -> Optional[Trace]:
    prog = syntax.the_program
    inits = tuple(init.expr for init in prog.inits())
    m = check_implication(solver, inits, [p], minimize=minimize)
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

def check_transition(
        s: Solver,
        old_hyps: Iterable[Expr],
        new_conc: Expr,
        minimize: Optional[bool] = None,
        timeout: int = 0,
)-> Optional[Trace]:
    t = s.get_translator(KEY_NEW, KEY_OLD)
    prog = syntax.the_program
    start = time.time()
    with s:
        for h in old_hyps:
            s.add(t.translate_expr(h, old=True))

        s.add(z3.Not(t.translate_expr(new_conc)))

        for trans in prog.transitions():
            with s:
                s.add(t.translate_transition(trans))

                # if utils.logger.isEnabledFor(logging.DEBUG):
                #     utils.logger.debug('assertions')
                #     utils.logger.debug(str(s.assertions()))
                res = s.check(timeout=timeout)
                if res == z3.sat:
                    #print(f"Found model in {time.time() - start:0.3f} sec")
                    return two_state_trace_from_z3(s.model(minimize=minimize))
                assert res == z3.unsat
    #print(f"Found model in {time.time() - start:0.3f} sec")                    
    return None

def check_two_state_implication_generalized(
        s: Solver,
        trans: DefinitionDecl,
        old_hyps: Iterable[Expr],
        new_conc: Expr,
        minimize: Optional[bool] = None,
        timeout: int = 0,
) -> Tuple[z3.CheckSatResult, Optional[z3.ModelRef]]:
    t = s.get_translator(KEY_NEW, KEY_OLD)
    with s:
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

async def async_recv(conn: Connection) -> Any:
    loop = asyncio.get_event_loop()
    event = asyncio.Event()
    try:
        loop.add_reader(conn.fileno(), event.set)
        await event.wait()
        return conn.recv()
    finally:
        # We need to do this in finally so that if we are cancelled, the
        # reader is removed. This is because for some reason the asyncio
        # loop can have at most one reader per fileno, and adding another
        # seems to silently do nothing.
        loop.remove_reader(conn.fileno())
    

T = TypeVar('T')
async def async_race(aws: Sequence[Awaitable[T]]) -> T:
    '''Returns the first value from `aws` and cancels the other tasks.
    
    Ignores exceptions from the awaitables, unless all awaitables produce an exception,
    which causes `async_race` to raise the exception from an arbitrary task.
    `aws` must be non-empty. '''
    while True:
        done, pending = await asyncio.wait(aws, return_when=asyncio.FIRST_COMPLETED)
        exc: Optional[BaseException] = None
        for f in done:
            if f.cancelled():
                exc = CancelledError()
            elif f.exception() is None:
                for unfinished in pending:
                    unfinished.cancel()
                return f.result()
            else:
                exc = f.exception()
        if len(pending) == 0:
            if exc is not None:
                raise exc
            else:
                raise ValueError("Empty sequence passed to async_race()")
        aws = list(pending)
            

async def multi_check_transition(old_hyps: Iterable[Expr],
        new_conc: Expr,
        minimize: Optional[bool] = None,
        timeout: int = 0) -> Optional[Trace]:
    async def check(s: Solver, min: bool) -> Optional[Trace]:        
        
        # This function will be executed in a forked process
        def worker(conn: Connection) -> None:
            # time.sleep(random.random())
            conn.send(check_transition(s, old_hyps, new_conc, minimize=min, timeout=timeout))
            
        (conn_main, conn_worker) = multiprocessing.Pipe(duplex = True)
        p = Process(target=worker, args = (conn_worker,))
        try:
            p.start()
            v = await async_recv(conn_main)
            return v
        except CancelledError as e:
            if p.is_alive():
                p.kill()
            raise e
    z3solver = Solver(use_cvc4=False)
    cvc4solver = Solver(use_cvc4=True)
    t1 = asyncio.create_task(check(z3solver, min=True if minimize else False), name="z3")
    t2 = asyncio.create_task(check(cvc4solver, min=False), name="cvc4")
    return await async_race([t1, t2])
    # done, pending = await asyncio.wait([t2, t1], return_when=asyncio.FIRST_COMPLETED)
    # task = done.pop()
    # for not_complete in pending:
    #     not_complete.cancel()
    # if task.exception() is not None:
    #     print("Error, successful task returned an exception")
    #     assert False
    # # if task is t1:
    # #     print("z3 produced a result")
    # # else:
    # #     print("cvc4 produced a result")
    # return task.result()

async def multi_check_implication(hyps: Iterable[Expr],
        conc: Expr,
        minimize: Optional[bool] = None,
        timeout: int = 0) -> Optional[Trace]:
    async def check(s: Solver, min: bool) -> Optional[Trace]:
               
        # This function will be executed in a forked process
        def worker(conn: Connection) -> None:
            m = check_implication(s, hyps, [conc], minimize=min)
            conn.send(Trace.from_z3([KEY_ONE], m) if m is not None else None)

        (conn_main, conn_worker) = multiprocessing.Pipe(duplex = True)
        p = Process(target=worker, args = (conn_worker,))
        try:
            p.start()
            result = await async_recv(conn_main)
            return result
        except CancelledError as e:
            p.kill()
            raise e
    z3solver = Solver(use_cvc4=False)
    cvc4solver = Solver(use_cvc4=True)
    t1 = asyncio.create_task(check(z3solver, min=True if minimize else False), name="z3")
    t2 = asyncio.create_task(check(cvc4solver, min=False), name="cvc4")
    return await async_race([t1, t2])
    # done, pending = await asyncio.wait([t2, t1], return_when=asyncio.FIRST_COMPLETED)
    # task = done.pop()
    # for not_complete in pending:
    #     not_complete.cancel()
    # if task.exception() is not None:
    #     print("Error, successful task returned an exception")
    #     assert False
    # # if task is t1:
    # #     print("z3 produced a result")
    # # else:
    # #     print("cvc4 produced a result")
    # return task.result()


class IGQueryLogger(object):
    def __init__(self) -> None:
        self.name = f"ig-{''.join(random.choice('0123456789ABCDEF') for x in range(8))}.log"
        self.f = open(os.path.join(utils.args.log_dir, self.name) if utils.args.log_dir else os.devnull, "w")
        self.start_time = time.time()
        
    def _print(self, *s: Any, mirror: bool = False, flush: bool = False) -> None:
        print(*s, file=self.f, flush=flush)
        if mirror:
            print(*s, flush=flush)
    async def start(self, s: 'ParallelFolIc3', frame: int, state: int) -> None:
        self._print(f"Inductive generalizing to block {state} in frame {frame}", mirror=True)
        if utils.args.log_dir:
            print(f"Inductive generalize log in {self.name}")
        
        tr = s._states[state]
        st = tr[0].as_state(tr[1])
        size_summary = ', '.join(f"|{sort.name}|={len(elems)}" for sort, elems in st.univs.items())
        self._print(f"Size of state to block {size_summary}")
        # golden: List[separators.logic.Formula] = []
        for inv in syntax.the_program.invs():
            if s._states[state][0].as_state(s._states[state][1]).eval(inv.expr) == False:
                cex = await multi_check_transition([*(s._predicates[j] for j in s.frame_predicates(frame-1)), inv.expr], inv.expr, minimize=False)
                # g_as_formula = predicate_to_formula(inv.expr)
                # golden.append(g_as_formula)
                self._print("Possible formula is:", inv.expr, '(relatively inductive)' if cex is None else '(not relatively inductive)')
        self.f.flush()
    def found_edge(self, edge: Trace) -> None:
        self._print("Adding new edge", flush=True, mirror=True)
    def found_intial(self, state: Trace) -> None:
        self._print("Adding new initial state", flush=True, mirror=True)
    def found_candidate(self, p: Expr, origin: str) -> None:
        self._print(f"Candidate (from {origin}) {p}", mirror=True)
    def learned(self, p: Expr) -> None:
        self._print(f"Learned new predicate {p}", mirror=True)
        self._print(f"Elapsed: {time.time() - self.start_time}", flush=True)
        self.f.close() 




class ParallelFolIc3(object):
    FrameNum = Optional[int]
    def __init__(self) -> None:
        self._solver = Solver(use_cvc4=utils.args.cvc4)

        self._states: List[PDState] = []
        self._initial_states: Set[int] = set()
        self._transitions: Set[Tuple[int, int]] = set()
        self._successors: DefaultDict[int, Set[int]] = defaultdict(set)
        self._predecessors: DefaultDict[int, Set[int]] = defaultdict(set)
        
        self._predicates: List[Expr] = []
        self._frame_numbers: List[Optional[int]] = [] # the frame number for each predicate
        self._initial_conditions: Set[int] = set() # predicates that are initial conditions in F_0
        self._safeties: Set[int] = set() # predicates that are safety properties
        self._reachable: Set[int] = set()

        self._bad_predicates: Set[int] = set()
        self._unsafe: bool = False

        # Caches and derived information
        self._eval_cache: Dict[Tuple[int, int], bool] = {}
        self._pushing_blocker: Dict[int, int] = {}
        self._predecessor_cache: Dict[Tuple[int, int], int] = {}
        self._no_predecessors: Set[Tuple[int, int]] = set()
        self._reachable_worklist: Set[int] = set()

        # Synchronization
        self._event_frames = asyncio.Event()
        self._event_reachable = asyncio.Event()
        self._current_heuristic_tasks: Set[Tuple[int,int]] = set()


    # Frame number manipulations (make None === infinity)
    @staticmethod
    def frame_max(a: FrameNum, b: FrameNum) -> FrameNum:
        if a is None or b is None: return None
        return max(a,b)
    @staticmethod
    def frame_leq(a: FrameNum, b: FrameNum) -> bool:
        if b is None: return True
        if a is None: return False
        return a <= b
    @staticmethod
    def frame_key(a: FrameNum) -> Tuple[int, int]:
        if a is None: return (1, 0)
        return (0, a)

    # Evaluation and contents of frames
    def eval(self, pred: int, state: int) -> bool:
        if (pred, state) not in self._eval_cache:
            self._eval_cache[(pred, state)] = eval_predicate(self._states[state], self._predicates[pred])
        return self._eval_cache[(pred, state)]
    def frame_predicates(self, i: FrameNum) -> Iterable[int]:
        yield from (index for index, f in enumerate(self._frame_numbers) if ParallelFolIc3.frame_leq(i, f))
    def frame_transitions(self, i: FrameNum) -> Iterable[Tuple[int, int]]:
        yield from ((a, b) for a, b in self._transitions if all(self.eval(p, a) for p in self.frame_predicates(i)))
    
    # Termination conditions
    def is_complete(self) -> bool:
        return self.is_program_safe() or self.is_program_unsafe()
    def is_program_safe(self) -> bool:
        # Safe if all safeties have been pushed to F_inf
        return all(self._frame_numbers[i] is None for i in self._safeties)
    def is_program_unsafe(self) -> bool:
        return self._unsafe

    # Adding and manipulating states, transitions, and predicates
    def add_predicate(self, p: Expr, frame:int = 0) -> int:
        i = len(self._predicates)
        self._predicates.append(p)
        self._frame_numbers.append(frame)
        self._event_frames.set()
        self._event_frames.clear()
        return i
    def add_state(self, s: PDState) -> int:
        i = len(self._states)
        self._states.append(s)
        # print(f"State {i} is {s[0].as_state(s[1])}")
        return i  
    def add_transition(self, a:int, b:int) -> None:
        if (a,b) in self._transitions:
            return
        self._transitions.add((a,b))
        self._predecessors[b].add(a)
        self._successors[a].add(b)
        self._reachable_worklist.add(a)
        # self.push_reachable()


    def print_predicates(self) -> None:
        print ("[IC3] ---- Frame summary")
        for i, p, index in sorted(zip(self._frame_numbers, self._predicates, range(len(self._predicates))), key = lambda x: ParallelFolIc3.frame_key(x[0])):
            code = 'S' if index in self._safeties else 'i' if index in self._initial_conditions else 'b' if index in self._bad_predicates else ' '
            print(f"[IC3] predicate {i if i is not None else '+'} {code} {p}")
        print(f"[IC3] Reachable states: {len(self._reachable)}")
        print("[IC3] ----")

    def push_reachable(self, state:int) -> None:
        # Mark state reachable
        if state in self._reachable:
            return
        self._reachable.add(state)
        self._reachable_worklist.add(state)
        # Signal that we have changed reachablity
        self._event_reachable.set()
        self._event_reachable.clear()

        while len(self._reachable_worklist) > 0:
            item = self._reachable_worklist.pop()
            if item not in self._reachable:
                continue
            for b in self._successors[item]:
                if b not in self._reachable:
                    self._reachable.add(b)
                    self._reachable_worklist.add(b)
                    # Signal that we have changed reachablity
                    self._event_reachable.set()
                    self._event_reachable.clear()
            
    # Pushing
    async def push_once(self) -> bool:
        made_changes = False
        for index, p in sorted(enumerate(self._predicates), key = lambda x: ParallelFolIc3.frame_key(self._frame_numbers[x[0]])):
            # No need to push things already in F_inf
            i = self._frame_numbers[index]
            if i is None:
                continue
            if index in self._pushing_blocker:
                blocker = self._pushing_blocker[index]
                # Check if blocking state is reachable (thus we should never push)
                if blocker in self._reachable:
                    continue
                # Check if the blocker state is still in F_i
                if all(self.eval(F_i_pred, blocker) for F_i_pred in self.frame_predicates(i)):
                    continue
                # The blocker is invalidated
                del self._pushing_blocker[index]
            # Either there is no known blocker or it was just invalidated by some new predicate in F_i
            # Check if any new blocker exists
            # cex = check_transition(self._solver, list(self._predicates[j] for j in self.frame_predicates(i)), p, minimize=False)
            fp = set(self.frame_predicates(i))
            cex = await multi_check_transition(list(self._predicates[j] for j in fp), p, minimize='no-minimize-block' not in utils.args.expt_flags)
            if fp != set(self.frame_predicates(i)):
                # Set of predicates changed across the await call. To avoid breaking the meta-invariant, loop around for another iteration
                made_changes = True
                continue
            if cex is None:
                # print("Proven that:")
                # for j in self.frame_predicates(i):
                #     print(f"  {self._predicates[j]}")
                # print("implies wp of:")
                # print(f"  {p}")

                print(f"Pushed {p} to frame {i+1}")
                self._frame_numbers[index] = i + 1
                self._event_frames.set()
                self._event_frames.clear()
                made_changes = True
            else:
                # Add the blocker and the sucessor state. We need the successor state because
                # if we show the blocker is reachable, it is actually the successor that invalidates
                # the predicate
                blocker = self.add_state((cex, 0))
                blocker_successor = self.add_state((cex, 1))
                self.add_transition(blocker, blocker_successor)
                
                self._pushing_blocker[index] = blocker
        return made_changes 

    def check_for_f_infinity(self) -> bool:
        made_changes = False
        for i in range(max(x for x in self._frame_numbers if x is not None)):
            # Check to see if any frame
            if i in self._frame_numbers:
                continue
            # Frame has no predicates that aren't also in later frames. Move any such predicates to F_inf
            for index, p in enumerate(self._predicates):
                p_frame = self._frame_numbers[index]
                if p_frame is not None and i < p_frame:
                    print(f"Pushed {p} to frame inf")
                    self._frame_numbers[index] = None
                    made_changes = True
        return made_changes

    async def push(self) -> None:
        while True:
            pushed = await self.push_once()
            made_infinite = self.check_for_f_infinity()
            # We did something, so go see if more can happen
            if pushed or made_infinite:
                continue
            break

    def init(self) -> None:
        prog = syntax.the_program
        for init_decl in prog.inits():
            i = self.add_predicate(init_decl.expr)
            self._initial_conditions.add(i)
        for safety_decl in prog.safeties():
            i = self.add_predicate(safety_decl.expr)
            self._safeties.add(i)
            self._frame_numbers[i] = 1
        if 'free-lemma' in utils.args.expt_flags:
            for inv_decl in prog.invs():
                if inv_decl.name == 'free_lemma':
                    i = self.add_predicate(inv_decl.expr)
                    self._frame_numbers[i] = 1
  
    # async def cancel_if_blocked(self, frame: int, state: int, task: asyncio.Task) -> None:
    #     while True:
    #         if any(not self.eval(pred, state) for pred in self.frame_predicates(frame)):
    #             task.cancel()
    #         if task.done():
    #             return
    #         await self._event_frames.wait()  
    async def wait_blocked(self, frame: int, state: int) -> None:
        while True:
            if any(not self.eval(pred, state) for pred in self.frame_predicates(frame)):
                print(f"Finished waiting for state {state} in frame {frame}")
                return
            await self._event_frames.wait()  

    async def parallel_inductive_generalize_worker(self, name: str, local_states: List[PDState], constraints: List[Constraint], log: IGQueryLogger, frame: int, state: int, sep: Separator) -> Expr:
        log_filename = f"sep-{''.join(random.choice('0123456789ABCDEF') for x in range(8))}.log"
        def subprocess_worker(conn: Connection) -> None:
            # Redirect output to either a log or empty
            sys.stdout = open(os.path.join(utils.args.log_dir, log_filename) if utils.args.log_dir else os.devnull, "w")
            print(f"Log of separator {name} blocking a state in frame {frame}")
            print(f"pid: {os.getpid()}")
            states: List[PDState] = []
            s = FOLSeparator(states, sep=sep)
            t = UnlimitedTimer()
            gen = LatticeEdgeGeneralizer()
            solver = Solver()
            while True:
                v = conn.recv()
                if 'state' in v:
                    states.append(v['state'])
                if 'sep' in v:
                    pos, neg, imp = v['sep']
                    print(f"Separating with {len(pos) + len(neg) + len(imp)} constraints")
                    with t:
                        p = s.separate(pos, neg, imp, complexity=1000)
                    print(f"Found separator: {p}")
                    print(f"Total separation time so far: {t.elapsed()}")
                    sys.stdout.flush()
                    conn.send(p)
                if 'gen' in v:
                    (st, frame_exprs, p) = v['gen']
                    r = gen.find_generalized_implication(solver, st, frame_exprs, p)
                    if r is None:
                        conn.send(None)
                    else:
                        tr, _ = r
                        conn.send(tr)

        (conn_main, conn_worker) = multiprocessing.Pipe(duplex = True)
        proc = Process(target=subprocess_worker, args = (conn_worker,))
        states_seen = 0
        # Experiment: disable sharing
        constraints = list(constraints)
        local_states = list(local_states)
        try:
            proc.start()
            if utils.args.log_dir:
                print(f"Separation log in {log_filename} ({name})")
            while True:
                # Update any states in the worker
                while states_seen < len(local_states):
                    conn_main.send({'state': local_states[states_seen]})
                    states_seen += 1
                cs = ([c.s for c in constraints if isinstance(c, PositiveStruct)],
                      [c.s for c in constraints if isinstance(c, NegativeStruct)],
                      [(c.s,c.t) for c in constraints if isinstance(c, ImplicationStructs)])
                conn_main.send({'sep': cs})
                p = await async_recv(conn_main)
                log.found_candidate(p, name)
                
                # TODO: check existing constraints
                already_blocked = False
                # for c in constraints:
                #     if isinstance(c, PositiveStruct) and not local_states[c.s][0].as_state(local_states[c.s][1]).eval(p):
                #         already_blocked = True
                #         break
                #     elif isinstance(c, ImplicationStructs) and (local_states[c.s][0].as_state(local_states[c.s][1]).eval(p)) and not (local_states[c.t][0].as_state(local_states[c.t][1]).eval(p)):
                #         already_blocked = True
                #         break
                initial_reachable = set(self._reachable)
                for ist in self._initial_states | self._reachable:
                    if not self._states[ist][0].as_state(self._states[ist][1]).eval(p):
                        x = len(local_states)
                        local_states.append(self._states[ist])
                        constraints.append(PositiveStruct(x))
                        already_blocked = True
                        break
                if already_blocked:
                    print("Used existing constraint (initial or reachable state)")
                    continue
                # F_0 => p
                initial_state = await multi_check_implication(initial_conditions(), p, minimize='no-minimize-cex' not in utils.args.expt_flags)
                if initial_state is not None:
                    log.found_intial(initial_state)
                    s = self.add_state((initial_state,0))
                    self._initial_states.add(s)
                    i = len(local_states)
                    local_states.append((initial_state,0))
                    constraints.append(PositiveStruct(i))
                    continue
                
                # F_i-1 ^ p => wp(p)?
                frame_preds = set(self.frame_predicates(frame-1))
                
                if 'generalize-edges' in utils.args.expt_flags:
                    conn_main.send({'gen': (self._states[state], [self._predicates[x] for x in frame_preds], p)})
                    edge = await async_recv(conn_main)
                else: 
                    edge = await multi_check_transition([p, *(self._predicates[j] for j in frame_preds)], p, minimize='no-minimize-cex' not in utils.args.expt_flags)


                if frame_preds != set(self.frame_predicates(frame-1)) or initial_reachable != self._reachable:
                    # During the await of multi_check_transiton, another concurrent task has updated the frame or reachable states. Thus
                    # we can't be sure we have a correct solution, so go to the top and try again.
                    continue
                
                if edge is not None:
                    log.found_edge(edge)
                    a = len(local_states)
                    local_states.append((edge, 0))
                    b = len(local_states)
                    local_states.append((edge, 1))
                    constraints.append(ImplicationStructs(a,b))
                    continue

                # If we get here, then p is a solution to our inductive generalization query        
                return p
        finally:
            proc.kill()

    async def parallel_inductive_generalize(self, frame: int, state: int) -> None:
        local_states: List[PDState] = []
        constraints: List[Constraint] = []
        log = IGQueryLogger()
        await log.start(self, frame, state)
        
        # Seed our states with the state to block and known initial states
        local_states.append(self._states[state])
        constraints.append(NegativeStruct(0))
        for initial_state in self._initial_states:
            x = len(local_states)
            local_states.append(self._states[initial_state])
            constraints.append(PositiveStruct(x))

        sig = prog_to_sig(syntax.the_program, two_state=False)
        workers: List[Awaitable[Optional[Expr]]] = []
        workers.append(self.wait_blocked(frame, state))
        #cancellers: List[asyncio.Task] = []
        def L(n: str, logic: str, expt_flags: Set[str], blocked_symbols: Set[str]) -> None:
            ctor = ImplicationSeparator if 'impmatrix' in expt_flags else HybridSeparator
            backing_sep = ctor(sig, logic = logic, expt_flags= expt_flags | utils.args.expt_flags, blocked_symbols=list(blocked_symbols))
            task = asyncio.create_task(self.parallel_inductive_generalize_worker(n, local_states, constraints, log, frame, state, backing_sep))
            #cancellers.append(asyncio.create_task(self.cancel_if_blocked(frame, state, task)))
            workers.append(task)
        
        if utils.args.logic == 'fol':
            L('full', 'fol', set(), set())
            # L('alt1', 'fol', set(['alternation1']), set())
            # L('m4', 'fol', set(['matrixsize4']), set())
            # L(WorkerArgs('imp', 'fol', set(['impmatrix']), blocked_symbols))
        
        L('A-full', 'universal', set(), set())
        # L('A-m4', 'universal', set(['matrixsize4']), set())
        # L('A-full-bdc', 'universal', set([]), set(['decision_quorum']))

        p = await async_race(workers)
        if p is None or any(not self.eval(pred, state) for pred in self.frame_predicates(frame)):
            print(f"State {state} was blocked in frame {frame} by concurrent task")
            return
        print(f"Found predicate to block {state} in frame {frame}")
        log.learned(p)
        self.add_predicate(p, frame)
        await self.push()
        self.print_predicates()
        


    async def inductive_generalize(self, frame: int, state: int) -> None:
        local_states: List[PDState] = []
        sep = FOLSeparator(self._states, local_states)
        edges: List[Tuple[int, int]] = []
        log = IGQueryLogger()
        await log.start(self, frame, state)
        while True:
            p = sep.separate(pos=self._initial_states, neg=[state], imp=edges, complexity=1000)
            if p is not None:
                log.found_candidate(p, "sep")
                # F_0 => p
                initial_state = await multi_check_implication(initial_conditions(), p, minimize=True)
                if initial_state is not None:
                    await log.found_intial(initial_state)
                    s = self.add_state((initial_state,0))
                    self._initial_states.add(s)
                    continue
                
                # F_i-1 ^ p => wp(p)?
                # gen = TrivialEdgeGeneralizer()
                # res = gen.find_generalized_implication(self._solver, self._states[state], [self._predicates[j] for j in self.frame_predicates(frame-1)], p)
                # edge = check_transition(self._solver, [p, *(self._predicates[j] for j in self.frame_predicates(frame-1))], p, minimize=True)
                edge = await multi_check_transition([p, *(self._predicates[j] for j in self.frame_predicates(frame-1))], p, minimize=True)
                if edge is not None:
                    log.found_edge(edge)
                    # s_i = self.add_state((edge,0))
                    # s_j = self.add_state((edge,1))
                    # self.add_transition(s_i, s_j)
                    # edges.append((s_i, s_j))
                    a = -(len(local_states) + 1)
                    local_states.append((edge, 0))
                    b = -(len(local_states) + 1)
                    local_states.append((edge, 1))
                    edges.append((a,b))
                    continue

                # If we get here, then p is a solution to our inductive generalization query        
                log.learned(p)
                self.add_predicate(p, frame)
                return
            else:
                assert False

    async def get_predecessor(self, frame: int, state: int) -> Optional[int]:
        assert frame != 0
        key = (frame-1, state)
        if key in self._no_predecessors:
            return None
        if key in self._predecessor_cache:
            pred = self._predecessor_cache[key]
            if all(self.eval(p, pred) for p in self.frame_predicates(frame - 1)):
                return pred
            del self._predecessor_cache[key]

        # First, look for any known predecessors of the state
        for pred in self._predecessors[state]:
            if all(self.eval(p, pred) for p in self.frame_predicates(frame - 1)):
                self._predecessor_cache[key] = pred
                return pred            

        # We need to check for a predecessor
        s = self._states[state]
        formula_to_block = Not(s[0].as_onestate_formula(s[1])) \
                        if utils.args.logic != "universal" else \
                        Not(s[0].as_diagram(s[1]).to_ast())
        # edge = check_transition(self._solver, [self._predicates[i] for i in self.frame_predicates(frame-1)], formula_to_block, minimize=False)
        edge = await multi_check_transition([self._predicates[i] for i in self.frame_predicates(frame-1)], formula_to_block, minimize='no-minimize-block' not in utils.args.expt_flags)
        if edge is None:
            self._no_predecessors.add(key)
            return None
        
        pred = self.add_state((edge, 0))
        self.add_transition(pred, state)
        self._predecessor_cache[key] = pred
        return pred
       

    async def block(self, frame: int, state: int) -> None:
        print(f"Block: {state} in frame {frame}")
        if frame == 0:
            assert all(self.eval(i, state) for i in self._initial_conditions)
            initial_reachable = set(self._reachable)
            self.push_reachable(state)
            print(f"Now have {len(self._reachable)} reachable states")
            # Mark any predicates as bad that don't satisfy all the reachable states
            for new_r in self._reachable - initial_reachable:
                print(f"New reachable state: {new_r}")
                st = self._states[new_r][0].as_state(self._states[new_r][1])
                for index, p in enumerate(self._predicates):
                    if not st.eval(p):
                        self._bad_predicates.add(index)
            self.print_predicates()
            return
        pred = await self.get_predecessor(frame, state)
        if pred is None:
            await self.parallel_inductive_generalize(frame, state)
        else:
            await self.block(frame - 1, pred)

    async def blockable_state(self, frame: int, state: int) -> Optional[Tuple[int, int]]:
        if frame == 0:
            assert all(self.eval(i, state) for i in self._initial_conditions)
            initial_reachable = set(self._reachable)
            self.push_reachable(state)
            # Mark any predicates as bad that don't satisfy all the reachable states
            for new_r in self._reachable - initial_reachable:
                print(f"New reachable state: {new_r}")
                st = self._states[new_r][0].as_state(self._states[new_r][1])
                for index, p in enumerate(self._predicates):
                    if not st.eval(p):
                        self._bad_predicates.add(index)
            return None
        pred = await self.get_predecessor(frame, state)
        if pred is None:
            return (frame, state)
        else:
            return await self.block(frame - 1, pred)

    def heuristically_blockable(self, pred: int) -> bool:
        if pred in self._safeties or pred in self._initial_conditions or pred in self._bad_predicates:
            return False
        fn = self._frame_numbers[pred]
        if fn is None or pred not in self._pushing_blocker:
            return False
        st = self._pushing_blocker[pred]
        if st in self._reachable:
            return False
        return True

    async def heuristic_pushing_to_the_top_worker(self, kind: bool) -> None:
        while True:
            priorities = random.sample(range(len(self._predicates)), len(self._predicates)) if kind \
                         else sorted(range(len(self._predicates)), key=lambda pred: ParallelFolIc3.frame_key(self._frame_numbers[pred]), reverse=kind)
            for pred in priorities:
                if not self.heuristically_blockable(pred):
                    continue
                fn, st = self._frame_numbers[pred], self._pushing_blocker[pred]
                if (fn, st) in self._current_heuristic_tasks:
                    continue
                print(f"Heuristically blocking state {st} in frame {fn}")
                self._current_heuristic_tasks.add((fn, st))
                try:
                    await self.block(fn, st)
                finally:
                    self._current_heuristic_tasks.remove((fn, st))
                break
            else:
                await self._event_frames.wait()

    async def inexpensive_reachability(self) -> None:
        while True:
            await self._event_frames.wait()
            for pred in range(len(self._predicates)):
                if not self.heuristically_blockable(pred):
                    continue
                fn, st = self._frame_numbers[pred], self._pushing_blocker[pred]
                
                # This has the side effect of finding a reachable path if one exists
                r = await self.blockable_state(fn, st)
                if r is None and st in self._reachable:
                    print("Inexpensive reachability found a new reachable state")
                    

                

    # This is the main loop responsible for learning classic IC3 lemmas by blocking bad states or backwardly reachable from bad
    async def learn(self) -> None:
        for safety in sorted(self._safeties, key = lambda x: ParallelFolIc3.frame_key(self._frame_numbers[x])):
            fn = self._frame_numbers[safety]
            # This is called after push, so if either of these is not satisfied we should have exited
            assert fn is not None
            if safety not in self._pushing_blocker:
                print(f"Cannot learn because pushing not yet complete")
                await self.push()
                return
            blocker = self._pushing_blocker[safety]
            print(f"Blocking {blocker} in frame {fn} for learning")
            await self.block(fn, blocker)
            return
        assert False

    async def run(self) -> None:
        print(f"ParallelFolIc3 log for {os.path.basename(utils.args.filename)}")
        print(f"Command line: {' '.join(sys.argv)}")
        start = time.time()
        self.init()
        await self.push()
        self.print_predicates()
        hueristics = [asyncio.create_task(self.heuristic_pushing_to_the_top_worker(False)), 
                      asyncio.create_task(self.heuristic_pushing_to_the_top_worker(True)),
                      asyncio.create_task(self.inexpensive_reachability())]
        while True:
            print(f"time: {time.time() - start:0.2f} sec")
            if self.is_complete():
                break
            # We need to block with a new predicate.
            await self.learn()

        for h in hueristics:
            h.cancel()
        print(f"Elapsed: {time.time() - start:0.2f} sec")
        if self.is_program_safe():
            print("Program is SAFE.")
            for i, p, index in zip(self._frame_numbers, self._predicates, range(len(self._predicates))):
                if i is None and index not in self._safeties:
                    print(f"  invariant [inferred] {p}")
        elif self.is_program_unsafe():
            print("Program is UNSAFE.")
        else:
            print("Program is UNKNOWN.")


def p_fol_ic3(solver: Solver) -> None:
    if utils.args.log_dir:
        os.makedirs(utils.args.log_dir, exist_ok=True)
    async def main():
        # We need to do this inside a function so that the events in the constructor of
        # p use the same event loop as p.run()
        p = ParallelFolIc3()
        await p.run()
    asyncio.run(main())
    
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
        # if check_implication(solver, I, [p], minimize=False) is None:
        #     I_imp_p = ">"
        # for i in I:
        #     if check_implication(solver, [p], [i], minimize=False) is None:
        #         p_imp_I = "<"
        #         break
        print(f"[IC3] Learned predicate (I{I_imp_p}{p_imp_I}p): {p}")

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
            backing_sep: Separator = ImplicationSeparator(sig, logic = args.logic, expt_flags= args.expt_flags, blocked_symbols=args.blocked_symbols)
        else:
            backing_sep = HybridSeparator(sig, logic = args.logic, expt_flags= args.expt_flags, blocked_symbols=args.blocked_symbols)
        local_states: List[PDState] = []
        constraints: List[Constraint] = []
        sep = FOLSeparator(local_states, sep=backing_sep)
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
        golden: List[separators.logic.Formula] = []
        for inv in syntax.the_program.invs():
            if states[t.state][0].as_state(states[t.state][1]).eval(inv.expr) == False:
                cex = check_two_state_implication_all_transitions(solver, [*frame_predicates(t.frame-1), inv.expr], inv.expr, minimize=False)
                g_as_formula = predicate_to_formula(inv.expr)
                golden.append(g_as_formula)
                print("Possible formula is:", g_as_formula, '(relatively inductive)' if cex is None else '(not relatively inductive)')
        
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
        L(WorkerArgs('Am2', 'universal', set(['matrixsize2']), []))

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
    if 'no-safeties' not in utils.args.expt_flags:
        for safety_decl in prog.safeties():
            predicates.append(safety_decl.expr)
            frame_numbers.append(0)
    if 'free-lemma' in utils.args.expt_flags:
        for inv_decl in prog.invs():
            if inv_decl.name == 'free_lemma':
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
                        print(f"[IC3] invariant {p}")
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

    s = subparsers.add_parser('p-fol-ic3', help='Run parallel IC3 inference with folseparators')
    s.set_defaults(main=p_fol_ic3)
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
        s.add_argument("--log-dir", dest="log_dir", type=str, default="", help="Log directory")

    return result