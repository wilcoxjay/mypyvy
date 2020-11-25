
from asyncio.exceptions import CancelledError
from io import TextIOBase
from typing import Any, Awaitable, DefaultDict, Dict, Iterable, Sequence, TextIO, List, Optional, Set, Tuple, Union, cast

import argparse
import subprocess
import sys
import os
import random
import time
import io
import pickle
import asyncio
import itertools
from collections import Counter, defaultdict
import typing
import networkx # type: ignore

import z3
from async_tools import AsyncConnection, ScopedProcess, ScopedTask, async_race
import utils
import logic
from logic import Expr, Solver, Trace, check_implication
import syntax
from syntax import BinaryExpr, DefinitionDecl, IfThenElse, Let, NaryExpr, QuantifierExpr, UnaryExpr
from fol_trans import eval_predicate, formula_to_predicate, predicate_to_formula, prog_to_sig, PDState, state_to_model
from separators import Constraint, Neg, Pos, Imp
from separators.separate import FixedImplicationSeparator, Logic, PrefixConstraints, PrefixSolver

def check_transition(
        s: Solver,
        old_hyps: Iterable[Expr],
        new_conc: Expr,
        minimize: Optional[bool] = None,
        timeout: int = 0,
        transition: Optional[DefinitionDecl] = None
)-> Optional[Trace]:
    t = s.get_translator(logic.KEY_NEW, logic.KEY_OLD)
    prog = syntax.the_program
    # start = time.time()
    with s:
        for h in old_hyps:
            s.add(t.translate_expr(h, old=True))

        s.add(z3.Not(t.translate_expr(new_conc)))

        for trans in prog.transitions():
            if transition is not None and trans is not transition:
                continue
            with s:
                s.add(t.translate_transition(trans))

                # if utils.logger.isEnabledFor(logging.DEBUG):
                #     utils.logger.debug('assertions')
                #     utils.logger.debug(str(s.assertions()))
                res = s.check(timeout=timeout)
                if res == z3.sat:
                    #print(f"Found model in {time.time() - start:0.3f} sec")
                    return Trace.from_z3([logic.KEY_OLD, logic.KEY_NEW], s.model(minimize=minimize))
                assert res == z3.unsat
    #print(f"Found model in {time.time() - start:0.3f} sec")                    
    return None

async def multi_check_transition(old_hyps: Iterable[Expr], new_conc: Expr, minimize: Optional[bool] = None, transition: Optional[DefinitionDecl] = None) -> Optional[Trace]:
    # graph = syntax.the_program.decls_quantifier_alternation_graph(list(old_hyps) + [syntax.Not(new_conc)])
    # if not networkx.is_directed_acyclic_graph(graph):
    #     print('ERROR -- Not in EPR! (trans)')
    #     for hyp in old_hyps:
    #         print(hyp)
    #     print(new_conc)
    #     print(' --- ')
    prefix = "/tmp"#  if utils.args.log_dir == "" else utils.args.log_dir
    file = os.path.join(prefix, f"query-{random.randint(0,1000000000-1):09}.pickle")
    with open(file, 'wb') as f:
        pickle.dump((old_hyps, new_conc, minimize, transition.name if transition is not None else None), f, protocol=pickle.HIGHEST_PROTOCOL)

    async def check(use_cvc4: bool, min: bool) -> Optional[Trace]:
        async def worker(conn: AsyncConnection) -> None:
            s = Solver(use_cvc4=use_cvc4)
            await conn.send(check_transition(s, old_hyps, new_conc, minimize=min, transition=transition))
        with ScopedProcess(worker) as conn:
            r = await conn.recv()
            return r
    try:
        start = time.time()
        result =  await async_race([check(use_cvc4=False, min=True if minimize else False),
                                check(use_cvc4=True, min=False)])
        return result
    finally:
        elapsed = time.time() - start
        if elapsed < 5:
            os.remove(file)
        else:
            os.rename(file, os.path.join(prefix, f"hard-query-{int(elapsed):04d}-{random.randint(0,1000000000-1):09}.pickle"))
    

async def robust_check_transition(old_hyps: Iterable[Expr], new_conc: Expr, minimize: Optional[bool] = None, transition: Optional[DefinitionDecl] = None) -> Optional[Trace]:
    pass

async def multi_check_implication(hyps: Iterable[Expr], conc: Expr, minimize: Optional[bool] = None) -> Optional[Trace]:
    # graph = syntax.the_program.decls_quantifier_alternation_graph(list(hyps) + [syntax.Not(conc)])
    # if not networkx.is_directed_acyclic_graph(graph):
    #     print('ERROR -- Not in EPR! (impl)')
    #     for hyp in hyps:
    #         print(hyp)
    #     print(conc)
    #     print(' --- ')
   
    async def check(use_cvc4: bool, min: bool) -> Optional[Trace]:
        async def worker(conn: AsyncConnection) -> None:
            s = Solver(use_cvc4=use_cvc4)
            m = check_implication(s, hyps, [conc], minimize=min)
            await conn.send(Trace.from_z3([logic.KEY_ONE], m) if m is not None else None)
        with ScopedProcess(worker) as conn:
            return await conn.recv()
    return await async_race([check(use_cvc4=False, min=True if minimize else False),
                             check(use_cvc4=True, min=False)])

async def IG_query_summary(x: TextIO, s: 'ParallelFolIc3', frame: int, state: int, rationale: str) -> Optional[Expr]:
    print(f"Inductive generalize blocking {state} in frame {frame} for {rationale}", file=x)
    tr = s._states[state]
    st = tr[0].as_state(tr[1])
    size_summary = ', '.join(f"|{sort.name}|={len(elems)}" for sort, elems in st.univs.items())
    print(f"Size of state to block {size_summary}", file=x)
    # golden: List[Formula] = []
    f: Optional[Expr] = None
    for inv in syntax.the_program.invs():
        if s._states[state][0].as_state(s._states[state][1]).eval(inv.expr) == False:
            cex = await multi_check_transition([*(s._predicates[j] for j in s.frame_predicates(frame-1)), inv.expr], inv.expr, minimize=False)
            print("Possible formula is:", inv.expr, '(relatively inductive)' if cex is None else '(not relatively inductive)', file=x)
            if cex is None:
                f = inv.expr
    return f

def satisifies_constraint(c: Constraint, p: Expr, states: Union[Dict[int, PDState], List[PDState]]) -> bool:
    if isinstance(c, Pos):
        if not eval_predicate(states[c.i], p):
            return False            
    elif isinstance(c, Neg):
        if eval_predicate(states[c.i], p):
            return False
    elif isinstance(c, Imp):
        if eval_predicate(states[c.i], p) and not eval_predicate(states[c.j], p):
            return False
    return True


class ParallelFolIc3(object):
    FrameNum = Optional[int]
    def __init__(self) -> None:
        # self._solver = Solver(use_cvc4=utils.args.cvc4)

        self._states: List[PDState] = [] # List of discovered states (excluding some internal cex edges)
        self._initial_states: Set[int] = set() # States satisfying the initial conditions
        self._transitions: Set[Tuple[int, int]] = set() # Set of transitions between states (s,t)
        self._successors: DefaultDict[int, Set[int]] = defaultdict(set) # Successors t of s in s -> t
        self._predecessors: DefaultDict[int, Set[int]] = defaultdict(set) # Predecessors s of t in s -> t
        
        self._predicates: List[Expr] = [] # List of predicates discovered
        self._frame_numbers: List[Optional[int]] = [] # the frame number for each predicate
        self._initial_conditions: Set[int] = set() # predicates that are initial conditions in F_0
        self._safeties: Set[int] = set() # predicates that are safety properties
        self._reachable: Set[int] = set() # Known reachable states (not necessarily including initial states)
        self._useful_reachable: Set[int] = set() # Known reachable states that we think are useful as constraints

        self._bad_predicates: Set[int] = set() # Predicates that violate a known reachable state
        self._redundant_predicates: Set[int] = set() # Predicates implied by another predicate in F_inf
        self._unsafe: bool = False # Is the system unsafe? Used for termination TODO: actually set this flag

        # Caches and derived information
        self._eval_cache: Dict[Tuple[int, int], bool] = {} # Record eval for a (predicate, state)
        self._pushing_blocker: Dict[int, int] = {} # State for a predicate in F_i that prevents it pushing to F_i+1
        self._former_pushing_blocker: DefaultDict[int, Set[int]] = defaultdict(set) # Pushing blockers from prior frames
        self._pulling_blocker: Dict[int, Tuple[int, int]] = {} # State for a predicate in F_i that prevents it pulling to F_i-1
        self._predecessor_cache: Dict[Tuple[int, int], int] = {} # For (F_i, state) gives s such that s -> state is an edge and s in F_i
        self._no_predecessors: Dict[int, Set[int]] = {} # Gives the set of predicates that block all predecessors of a state

        # Synchronization
        self._event_frames = asyncio.Event() # Signals when a frame is updated, either with a learned predicate or a push/pull
        self._event_reachable = asyncio.Event() # Signals when the set of reachable states changes
        self._current_push_heuristic_tasks: Set[Tuple[int,int]] = set() # Which (frame, state) pairs are being worked on by the push heuristic?
        self._current_pull_heuristic_tasks: Set[Tuple[int,int]] = set() # Which (frame, state) pairs are being worked on by the pull heuristic?
        self._push_pull_lock = asyncio.Lock()
        
        # Logging, etc
        self._start_time: float = 0
        self._sep_log: TextIO = sys.stdout if utils.args.log_dir == '' else open(os.path.join(utils.args.log_dir, 'sep.log'), 'w')
        self._ig_log: TextIO = sys.stdout if utils.args.log_dir == '' else open(os.path.join(utils.args.log_dir, 'ig.log'), 'w')
        self._next_ig_query_index = 0
        
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
        # Warning: this method does not compute new reachability. In all current uses, the
        # state a is a new state that cannot be known to be reachable, so this is safe.
        # If a method of determing new transitions between existing states is added, it must
        # call push_reachable to update reachability information.


    def print_predicates(self) -> None:
        print ("[IC3] ---- Frame summary")
        # cnt = len([i for (i,fn) in enumerate(self._frame_numbers) if fn == 0 and i in self._bad_predicates])
        # print(f"[IC3] predicate  0 b ... (x{cnt})")
        for i, p, index in sorted(zip(self._frame_numbers, self._predicates, range(len(self._predicates))), key = lambda x: ParallelFolIc3.frame_key(x[0])):
            if i == 0 and index in self._bad_predicates:
                continue
            code = '$' if index in self._safeties else 'i' if index in self._initial_conditions else 'b' if index in self._bad_predicates else ' '
            fn_str = f"{i:2}" if i is not None else ' +'
            print(f"[IC3] predicate {fn_str} {code} {p}")
        print(f"[IC3] Reachable states: {len(self._reachable)}, initial states: {len(self._initial_states)}, useful reachable: {len(self._useful_reachable)}")
        print("[IC3] ----")
        print(f"time: {time.time() - self._start_time:0.2f} sec")

    def push_reachable(self, state:int) -> None:
        # Mark state reachable
        if state in self._reachable:
            return
        self._reachable.add(state)
        _reachable_worklist = set([state])
        # Signal that we have changed reachablity
        self._event_reachable.set()
        self._event_reachable.clear()

        while len(_reachable_worklist) > 0:
            item = _reachable_worklist.pop()
            if item not in self._reachable:
                continue
            for b in self._successors[item]:
                if b not in self._reachable:
                    self._reachable.add(b)
                    _reachable_worklist.add(b)
                    # Signal that we have changed reachablity
                    self._event_reachable.set()
                    self._event_reachable.clear()
            
    # Pushing
    async def push_once(self) -> bool:
        made_changes = False
        for index, p in sorted(enumerate(self._predicates), key = lambda x: ParallelFolIc3.frame_key(self._frame_numbers[x[0]])):
            # No need to push things already in F_inf
            i = self._frame_numbers[index]
            if i is None or index in self._bad_predicates:
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
                self._former_pushing_blocker[index].add(self._pushing_blocker[index])
                del self._pushing_blocker[index]
            # Either there is no known blocker or it was just invalidated by some new predicate in F_i
            # First check if any former blockers still work
            for former_blocker in self._former_pushing_blocker[index]:
                if all(self.eval(F_i_pred, former_blocker) for F_i_pred in self.frame_predicates(i)):
                    print(f"Using former blocker {former_blocker}")
                    self._pushing_blocker[index] = former_blocker
            # We found a former one to use
            if index in self._pushing_blocker:
                continue


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
                # the predicate and is required to mark it as bad
                blocker = self.add_state((cex, 0))
                blocker_successor = self.add_state((cex, 1))
                self.add_transition(blocker, blocker_successor)
                
                self._pushing_blocker[index] = blocker
                # Signal here so that heuristic tasks waiting on a pushing_blocker can be woken
                self._event_frames.set()
                self._event_frames.clear()
        return made_changes 

    async def pull_once(self) -> bool:
        made_changes = False
        for index, p in sorted(enumerate(self._predicates), key = lambda x: ParallelFolIc3.frame_key(self._frame_numbers[x[0]]), reverse=True):
            fn = self._frame_numbers[index]
            # No need to pull things that aren't bad, already only in F_0 or not in F_inf
            if fn is None or fn == 0 or index not in self._bad_predicates:
                continue
            if index in self._pulling_blocker:
                blocker, dependant_pred = self._pulling_blocker[index]
                # Check if blocking state is reachable. TODO: what does this mean?
                if blocker in self._reachable:
                    print(f"Pulling blocker was reachable for state {blocker} in frame {fn} ???")
                    continue
                # Check if the blocker state is still in F_i \ p and if the dependent predicate is in the next frame
                if all(self.eval(F_i_pred, blocker) for F_i_pred in self.frame_predicates(fn) if F_i_pred != index):
                    continue
                if dependant_pred in self.frame_predicates(fn + 1):
                    continue
                # The blocker is invalidated
                del self._pulling_blocker[index]
            # Either there is no known blocker or it was just invalidated; check if any new blocker exists
            fp = set(self.frame_predicates(fn)).difference([index])
            fp_next = set(self.frame_predicates(fn+1)).difference(self.frame_predicates(fn+2))
            cex: Optional[Trace] = None
            dependent_pred = -1
            for q in fp_next:
                cex = await multi_check_transition(list(self._predicates[j] for j in fp), self._predicates[q], minimize='no-minimize-block' not in utils.args.expt_flags)
                if cex is not None:
                    dependent_pred = q
                    break
            # Check if set of predicates changed across the await call. To avoid breaking the meta-invariant, loop around for another iteration if so
            if fp != set(self.frame_predicates(fn)).difference([index]) or fp_next != set(self.frame_predicates(fn+1)).difference(self.frame_predicates(fn+2)):
                made_changes = True
                continue
            if cex is None:
                print(f"Pulled {p} to frame {fn - 1}")
                self._frame_numbers[index] = fn - 1
                self._event_frames.set()
                self._event_frames.clear()
                made_changes = True
            else:
                blocker = self.add_state((cex, 0))
                # Unlike pushing, we don't need to add the sucessor state because we don't expect either to
                # be reachable.
                # blocker_successor = self.add_state((cex, 1))
                # self.add_transition(blocker, blocker_successor)
                self._pulling_blocker[index] = (blocker, dependent_pred)
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

    async def push_pull(self) -> None:
        async with self._push_pull_lock:
            while True:
                pushed = await self.push_once()
                pulled = (await self.pull_once()) if 'pulling' in utils.args.expt_flags else False
                made_infinite = self.check_for_f_infinity()
                # We did something, so go see if more can happen
                if pushed or pulled or made_infinite:
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

    async def wait_blocked(self, frame: int, state: int, ignored_pred: int = -1) -> None:
        while True:
            if not all(self.eval(pred, state) for pred in self.frame_predicates(frame) if pred != ignored_pred):
                return
            await self._event_frames.wait()  

    async def IG2_worker(self, conn: AsyncConnection) -> None:
        sig = prog_to_sig(syntax.the_program, two_state=False)
        sep = FixedImplicationSeparator(sig, (), PrefixConstraints(), 0, set(), [])
        constraints: Set[Constraint] = set()
        sep_constraints: Set[Constraint] = set()
        mapping: Dict[int, int] = {}
        states: Dict[int, PDState] = {}
        while True:
            v = await conn.recv()
            if 'prefix' in v:
                (prefix, pc) = v['prefix']
                del sep
                sep = FixedImplicationSeparator(sig, prefix, pc, 1, set(), [])
                sep_constraints = set()
                mapping = {}
            if 'constraints' in v:
                (cons, extra_states) = v['constraints']
                states.update(extra_states)
                constraints = set(cons)
            if 'sep' in v:
                minimized = False
                while True:
                    sep_r = sep.separate(minimize=minimized)
                    if sep_r is None:
                        await conn.send({'unsep': sep_constraints})
                        break
                    
                    p = formula_to_predicate(sep_r)
                    # print(f"Internal candidate: {p}")
                    for c in constraints:
                        if c in sep_constraints: continue
                        if not satisifies_constraint(c, p, states):
                            # print(f"Adding internal constraint {c}")
                            for s in c.states():
                                if s not in mapping:
                                    mapping[s] = sep.add_model(state_to_model(states[s]))
                            sep.add_constraint(c.map(mapping))
                            sep_constraints.add(c)
                            minimized = False
                            break
                    else:
                        # All known constraints are satisfied
                        if not minimized:
                            minimized = True
                            continue # continue the loop, now asking for a minimized separator
                        else:
                            await conn.send({'candidate': p, 'constraints': sep_constraints})
                            break

    async def IG2_manager(self, frame: int, state: int, rationale: str) -> Expr:
        identity = self._next_ig_query_index
        self._next_ig_query_index += 1

        def ig_print(*args: Any, **kwargs: Any) -> None:
            print(f"[{rationale[0].upper()}({identity})]", *args, file=self._ig_log, flush=True)
            
        def states_of(cs: Sequence[Constraint]) -> Set[int]: return set(s for c in cs for s in c.states())
        sig = prog_to_sig(syntax.the_program, two_state=False)
        positive = self._initial_states | self._useful_reachable
        states = [self._states[state], *(self._states[i] for i in positive)]
        constraints = [Neg(0), *(Pos(i+1) for i in range(len(positive)))]
        
        popularity: typing.Counter[Constraint] = Counter()
        popularity[Neg(0)] = 1000 # ensure the state to block is always one of the first constraints
        
        prefix_solver = PrefixSolver(sig)
        frame_preds = set(self.frame_predicates(frame-1))
        
        local_eval_cache: Dict[Tuple[int, int], bool] = {}
        def local_eval(pred: int, local_state: int) -> bool:
            if (pred, local_state) not in local_eval_cache:
                local_eval_cache[(pred, local_state)] = eval_predicate(states[local_state], self._predicates[pred])
            return local_eval_cache[(pred, local_state)]

        solution: asyncio.Future[Expr] = asyncio.Future()
        
        async def check_candidate(p: Expr) -> Optional[Constraint]:
            # F_0 => p?
            initial_state = await multi_check_implication([init.expr for init in syntax.the_program.inits()], p, minimize='no-minimize-cex' not in utils.args.expt_flags)
            if initial_state is not None:
                ig_print("Adding initial state")
                i = len(states)
                states.append((initial_state, 0))
                # x = self.add_state((initial_state, 0))
                # self._initial_states.add(x)
                return Pos(i)
            
            # F_i-1 ^ p => wp(p)?
            start = time.time()
            edge = await multi_check_transition([p, *(self._predicates[fp] for fp in frame_preds)], p, minimize='no-minimize-cex' not in utils.args.expt_flags)
            ig_print(f"Check took {time.time()-start:0.3f}s")
            # if golden is not None and edge is not None:
            #     print(f"Golden {eval_predicate((edge, 0), golden)} -> {eval_predicate((edge, 1), golden)}")
            if edge is not None:
                ig_print("Adding edge")
                a = len(states)
                states.append((edge, 0))
                b = len(states)
                states.append((edge, 1))
                return Imp(a,b)

            # print("Found candidate")
            return None

        async def worker_handler(pc: PrefixConstraints) -> None:
            nonlocal solution, constraints, popularity

            with ScopedProcess(self.IG2_worker) as conn:
                # Keep track of which states the worker knows about, so we only send necessary ones
                worker_known_states: Set[int] = set()
                async def send_constraints(cs: Sequence[Constraint]) -> None:
                    new_states = states_of(cs).difference(worker_known_states)
                    extra_states = {i: states[i] for i in new_states}
                    worker_known_states.update(new_states)
                    # print(f"Constraints are: {cs}")
                    await conn.send({'constraints': (cs, extra_states)})
                
                local_constraints: List[Constraint] = []
                while True:
                    # Get a prefix from the solver
                    current_constr = local_constraints + constraints
                    pre = prefix_solver.get_prefix(current_constr, pc)
                    if pre is None:
                        return
                    pre_pp = ".".join(sig.sort_names[sort_i] for (ifa, sort_i) in pre)
                    ig_print(f"Trying: {pre_pp}")
                    reservation = prefix_solver.reserve(pre, pc)
                    await conn.send({'prefix': (pre, pc)})
                    while True:
                        current_constr = constraints + local_constraints
                        current_constr.sort(key = lambda x: popularity[x], reverse=True)
                        await send_constraints(current_constr)
                        await conn.send({'sep': None})
                        v = await conn.recv()
                        if 'candidate' in v:
                            p, sep_constraints = v['candidate'], v['constraints']
                            new_constraint = await check_candidate(p)
                            if new_constraint is None:
                                if not solution.done():
                                    ig_print(f"SEP with |constr|={len(sep_constraints)}")
                                    ig_print(f"Learned {p}")
                                    solution.set_result(p)
                                return
                            else:
                                # print(f"Adding {new_constraint}")
                                local_constraints.append(new_constraint)
                                # if golden is not None:
                                #     if not satisifies_constraints([new_constraint], golden, states):
                                #         print(f"! -- oops {new_constraint} isn't satisfied by {golden}")
                        elif 'unsep' in v:
                            core = v['unsep']
                            ig_print(f"UNSEP: {pre_pp} with |core|={len(core)}")
                            # if False:
                            #     test_sep = FixedImplicationSeparator(sig, pre, pc)
                            #     m = {i: test_sep.add_model(state_to_model(states[i])) for i in range(len(states))}
                            #     for c in cs:
                            #         test_sep.add_constraint(c.map(m))
                            #     assert test_sep.separate() is None
                            prefix_solver.unsep(core, pc, pre)
                            for c in core:
                                popularity[c] += 1
                            break
                        else:
                            assert False
                    # print(f"Done with: {pre}")
                    prefix_solver.unreserve(reservation)
        
        async def frame_updater() -> None:
            nonlocal constraints, frame_preds
            def in_frame(current_frame: Set[int], c: Constraint) -> bool:
                pass
                if isinstance(c, Imp):
                    return all(local_eval(fp, c.i) for fp in current_frame)
                else:
                    return True
            while True:
                current_frame = set(self.frame_predicates(frame-1))
                if frame_preds != current_frame:
                    constraints = [c for c in constraints if in_frame(current_frame, c)]
                    frame_preds = current_frame
                    if (await self.get_predecessor(frame, state)) is not None:
                        print("State to block has a predecessor via concurrent task", file=self._ig_log)
                        solution.cancel()
                else:
                    await self._event_frames.wait()

        async def logger() -> None:
            query_start = time.time()
            ig_print(f"started at: {query_start - self._start_time:0.2f}s")
            t = io.StringIO()
            golden = await IG_query_summary(t, self, frame, state, rationale)
            ig_print(t.getvalue(), end='')
            while True:
                try: await asyncio.sleep(30)
                except asyncio.CancelledError: 
                    ig_print(f"finished in: {time.time() - query_start:0.2f}s")
                    return
                ig_print(f"time: {time.time() - query_start:0.2f}s")


        if utils.args.logic == 'universal':
            pcs = [PrefixConstraints(Logic.Universal),
                   PrefixConstraints(Logic.Universal, max_repeated_sorts = 2),
                   PrefixConstraints(Logic.Universal, max_repeated_sorts = 2, min_depth=4),
                   PrefixConstraints(Logic.Universal, max_repeated_sorts = 2, min_depth=5),
                   PrefixConstraints(Logic.Universal, max_repeated_sorts = 2, min_depth=6),
                   PrefixConstraints(Logic.Universal, max_repeated_sorts = 2, min_depth=7),
                   PrefixConstraints(Logic.Universal, max_repeated_sorts = 3, min_depth=7)]
        elif utils.args.logic == 'epr':
            pcs = [PrefixConstraints(Logic.Universal, max_repeated_sorts=3),
                   PrefixConstraints(Logic.EPR, min_depth=0, max_alt=2, max_repeated_sorts=3),
                   PrefixConstraints(Logic.EPR, min_depth=6, max_alt=1, max_repeated_sorts=2),
                   PrefixConstraints(Logic.EPR, min_depth=7, max_alt=1, max_repeated_sorts=2),
                   PrefixConstraints(Logic.EPR, min_depth=8, max_alt=2, max_repeated_sorts=2),
                   PrefixConstraints(Logic.EPR, min_depth=8, max_alt=1, max_repeated_sorts=2)]
        elif utils.args.logic == 'fol':
            pcs = [PrefixConstraints(Logic.FOL),
                   PrefixConstraints(Logic.FOL, max_repeated_sorts = 2),
                   PrefixConstraints(Logic.FOL, max_repeated_sorts = 2, min_depth=4),
                   PrefixConstraints(Logic.FOL, max_repeated_sorts = 2, min_depth=5)]
        else:
            assert False
        for pc in pcs:
            if pc.logic == Logic.EPR:
                qe = [(sig.sort_indices[x], sig.sort_indices[y]) for (x,y) in itertools.product(sig.sort_names, sig.sort_names) if (x,y) not in utils.args.epr_edges]
                pc.disallowed_quantifier_edges = qe
        multiplier = 1
        handlers = [worker_handler(pc) for pc in pcs * multiplier]
        handlers.append(frame_updater())
        handlers.append(logger())

        async with ScopedTask(asyncio.gather(*handlers)):
            return await solution

    async def parallel_inductive_generalize2(self, frame: int, state: int, rationale: str = '') -> None:
        p = await async_race([cast(Awaitable[Optional[Expr]], self.wait_blocked(frame, state)),
                              self.IG2_manager(frame, state, rationale)])
        if p is None or any(not self.eval(pred, state) for pred in self.frame_predicates(frame)):
            print(f"State {state} was blocked in frame {frame} by concurrent task")
            return
        
        print(f"Learned new predicate {p} blocking {state} in frame {frame} for {rationale}")
        self.add_predicate(p, frame)
        await self.push_pull()
        self.print_predicates()

    async def get_predecessor(self, frame: int, state: int) -> Optional[int]:
        assert frame != 0
        key = (frame-1, state)
        if state in self._no_predecessors:
            if self._no_predecessors[state].issubset(self.frame_predicates(frame - 1)):
                return None
            # If we are not a subset of the current frame, then we might have predecessors
            del self._no_predecessors[state]
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
        formula_to_block = syntax.Not(s[0].as_onestate_formula(s[1])) \
                        if utils.args.logic != "universal" else \
                        syntax.Not(s[0].as_diagram(s[1]).to_ast())
        # We do this in a loop to ensure that if someone concurrently modifies the frames, we still compute a correct
        # predecessor.
        while True:
            fp = set(self.frame_predicates(frame-1))
            # edge = check_transition(self._solver, [self._predicates[i] for i in self.frame_predicates(frame-1)], formula_to_block, minimize=False)
            edge = await multi_check_transition([self._predicates[i] for i in fp], formula_to_block, minimize='no-minimize-block' not in utils.args.expt_flags)
            if fp != set(self.frame_predicates(frame-1)):
                continue
            break
        if edge is None:
            self._no_predecessors[state] = fp
            return None
        
        pred = self.add_state((edge, 0))
        self.add_transition(pred, state)
        self._predecessor_cache[key] = pred
        return pred
       
    def mark_reachable_and_bad(self, state: int, rationale: str = '') -> None:
        initial_reachable = set(self._reachable)
        self.push_reachable(state)
        new = self._reachable - initial_reachable
        if len(new) == 0:
            return
        print(f"Now have {len(self._reachable)} reachable states (for {rationale})")
        # Mark any predicates as bad that don't satisfy all the reachable states
        for new_r in new:
            print(f"New reachable state: {new_r}")
            st = self._states[new_r][0].as_state(self._states[new_r][1])
            for index, p in enumerate(self._predicates):
                if index not in self._bad_predicates and index not in self._initial_conditions and not st.eval(p):
                    print(f"Marked {p} as bad")
                    self._bad_predicates.add(index)
                    self._useful_reachable.add(new_r)
        self.print_predicates()
            
    async def block(self, frame: int, state: int, rationale: str) -> None:
        # print(f"Block: {state} in frame {frame} for {rationale}")
        if frame == 0:
            assert all(self.eval(i, state) for i in self._initial_conditions)
            self.mark_reachable_and_bad(state, rationale)
            return
        pred = await self.get_predecessor(frame, state)
        if pred is None:
            await self.parallel_inductive_generalize2(frame, state, rationale=rationale)
        else:
            await self.block(frame - 1, pred, rationale)

    async def blockable_state(self, frame: int, state: int, rationale: str) -> Optional[Tuple[int, int]]:
        if frame == 0:
            assert all(self.eval(i, state) for i in self._initial_conditions)
            self.mark_reachable_and_bad(state, rationale)
            return None
        pred = await self.get_predecessor(frame, state)
        if pred is None:
            return (frame, state)
        else:
            return await self.blockable_state(frame - 1, pred, rationale)

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
        # print("Starting heuristics")
        while True:
            priorities = random.sample(range(len(self._predicates)), len(self._predicates)) if kind \
                         else sorted(range(len(self._predicates)), key=lambda pred: ParallelFolIc3.frame_key(self._frame_numbers[pred]))
            # print("Checking for something to do")
            frame_N = min((self._frame_numbers[s] for s in self._safeties), key = ParallelFolIc3.frame_key)
            # print(f"Frame_N: {frame_N}")
            for pred in priorities:
                # Don't push anything past the earliest safety
                if self.frame_leq(frame_N, self._frame_numbers[pred]):
                    continue
                if not self.heuristically_blockable(pred):
                    continue
                fn, st = self._frame_numbers[pred], self._pushing_blocker[pred]
                assert fn is not None
                if (fn, st) in self._current_push_heuristic_tasks:
                    continue
                try:
                    self._current_push_heuristic_tasks.add((fn, st))
                    # print(f"Heuristically blocking state {st} in frame {fn}")
                    await self.block(fn, st, "heuristic-push")
                    # print("Finished heuristically pushing (block)")
                    await self.push_pull()
                    # print("Finished heuristically pushing (push_pull)")
                finally:
                    self._current_push_heuristic_tasks.remove((fn, st))
                break
            else:
                # print("Couldn't find job to do in heuristic-push")
                await self._event_frames.wait()
    
    async def inexpensive_reachability(self) -> None:
        while True:
            await self._event_frames.wait()
            for pred in range(len(self._predicates)):
                if not self.heuristically_blockable(pred):
                    continue
                fn, st = self._frame_numbers[pred], self._pushing_blocker[pred]
                assert fn is not None
                # This has the side effect of finding a reachable path if one exists
                r = await self.blockable_state(fn, st, "inexpensive-reachability")
        
    # This is the main loop responsible for learning classic IC3 lemmas by blocking bad states or backwardly reachable from bad
    async def learn(self) -> None:
        for safety in sorted(self._safeties, key = lambda x: ParallelFolIc3.frame_key(self._frame_numbers[x])):
            fn = self._frame_numbers[safety]
            # This is called after push, so if either of these is not satisfied we should have exited
            assert fn is not None
            if safety not in self._pushing_blocker:
                print(f"Cannot learn because pushing not yet complete")
                await self.push_pull()
                return
            blocker = self._pushing_blocker[safety]
            # print(f"Blocking {blocker} in frame {fn} for learning")
            await self.block(fn, blocker, "learning")
            return
        assert False

    async def run(self) -> None:
        self._start_time = time.time()
        self.init()
        await self.push_pull()
        self.print_predicates()
        hueristics = [asyncio.create_task(self.heuristic_pushing_to_the_top_worker(False)), 
                      asyncio.create_task(self.heuristic_pushing_to_the_top_worker(True)),
                      # asyncio.create_task(self.heuristic_pushing_to_the_top_worker(True)),
                      # asyncio.create_task(self.heuristic_pulling_to_the_bottom_worker(False)),
                      # asyncio.create_task(self.heuristic_pulling_to_the_bottom_worker(False)),
                      asyncio.create_task(self.inexpensive_reachability())]
        while True:
            if self.is_complete():
                break
            # We need to block with a new predicate.
            await self.learn()

        for h in hueristics:
            h.cancel()
        for h in hueristics:
            try: await h
            except asyncio.CancelledError: pass

        print(f"Elapsed: {time.time() - self._start_time:0.2f} sec")
        if self.is_program_safe():
            print("Program is SAFE.")
            for i, p, index in zip(self._frame_numbers, self._predicates, range(len(self._predicates))):
                if i is None and index not in self._safeties:
                    print(f"  invariant [inferred] {p}")
        elif self.is_program_unsafe():
            print("Program is UNSAFE.")
        else:
            print("Program is UNKNOWN.")

def p_fol_ic3(_: Solver) -> None:
    if utils.args.log_dir:
        os.makedirs(utils.args.log_dir, exist_ok=True)
        sys.stdout = io.TextIOWrapper(open(os.path.join(utils.args.log_dir, "main.log"), "wb"), line_buffering=False, encoding='utf8')
    print(f"ParallelFolIc3 log for {os.path.basename(utils.args.filename)}")
    print(f"Command line: {' '.join(sys.argv)}")
    try:
        path = os.path.dirname(os.path.realpath(__file__))
        wd = os.getcwd() if path == '' else path
        print(f"Hash: {subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=wd, encoding='utf8').strip()}")
    except (subprocess.CalledProcessError, FileNotFoundError):
        print(f"Hash: unknown")
    async def main() -> None:
        # We need to do this inside a function so that the events in the constructor of
        # p use the same event loop as p.run()
        p = ParallelFolIc3()
        await p.run()
    asyncio.run(main())

def fol_extract(solver: Solver) -> None:
    import os.path
    prog = syntax.the_program
    sig = prog_to_sig(prog)
    base_name = os.path.splitext(os.path.basename(utils.args.filename))[0].replace('_','-')
    
    if 'generate-problems' in utils.args.expt_flags:
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
    if utils.args.logic == 'epr':
        graph = prog.decls_quantifier_alternation_graph([x.expr for x in prog.invs()] + [syntax.Not(x.expr) for x in prog.invs()])
        print(f"Is acyclic: {networkx.is_directed_acyclic_graph(graph)}")
        arg = ','.join(f'{a}->{b}' for (a,b) in graph.edges)
        print(f"--epr-edges='{arg}'")
    
    def count_quantifiers(e: Expr) -> int:
        if isinstance(e, QuantifierExpr):
            return len(e.binder.vs) + count_quantifiers(e.body)
        elif isinstance(e, UnaryExpr):
            return count_quantifiers(e.arg)
        elif isinstance(e, BinaryExpr):
            return count_quantifiers(e.arg1) + count_quantifiers(e.arg2)
        elif isinstance(e, NaryExpr):
            return sum(count_quantifiers(a) for a in e.args)
        elif isinstance(e, IfThenElse):
            return count_quantifiers(e.branch) + count_quantifiers(e.then) + count_quantifiers(e.els)
        elif isinstance(e, Let):
            return count_quantifiers(e.body)
        else:
            return 0

    conjuncts, quants = 0, 0
    for x in prog.invs():
        if x.is_safety: continue
        conjuncts += 1
        quants = max(quants, count_quantifiers(x.expr))
    sig = prog_to_sig(syntax.the_program)
    print(f"{base_name}, {conjuncts}, {quants}, {len(sig.sorts)}, {len(sig.relations) + len(sig.constants) + len(sig.functions)}")

def fol_learn(solver: Solver) -> None:
    pass

def fol_benchmark_solver(solver: Solver) -> None:
    pass

def add_argparsers(subparsers: argparse._SubParsersAction) -> Iterable[argparse.ArgumentParser]:

    result : List[argparse.ArgumentParser] = []

    s = subparsers.add_parser('p-fol-ic3', help='Run parallel IC3 inference with folseparators')
    s.set_defaults(main=p_fol_ic3)
    result.append(s)

    s = subparsers.add_parser('fol-extract', help='Extract conjuncts to a file')
    s.set_defaults(main=fol_extract)
    result.append(s)


    s = subparsers.add_parser('fol-learn', help='Learn a given formula')
    s.set_defaults(main=fol_learn)
    result.append(s)

    s = subparsers.add_parser('fol-benchmark-solver', help='Test SMT solver backend')
    s.set_defaults(main=fol_benchmark_solver)
    result.append(s)


    def epr_edges(s: str) -> List[Tuple[str, str]]:
        r = []
        for pair in s.split(','):
            if pair.split() == '': continue
            parts = pair.split("->")
            if len(parts) != 2:
                raise ValueError("Epr edges must be of the form sort->sort, sort2 -> sort3, ...")
            r.append((parts[0].strip(), parts[1].strip()))
        return r

    for s in result:
        # FOL specific options
        s.add_argument("--logic", choices=('fol', 'epr', 'universal'), default="fol", help="Restrict form of separators to given logic (fol is unrestricted)")
        s.add_argument("--max-complexity", type=int, default=100, help="Maximum formula complexity")
        s.add_argument("--max-clauses", type=int, default=100, help="Maximum formula matrix clauses")
        s.add_argument("--max-depth", type=int, default=100, help="Maximum formula quantifier depth")
        s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: set(x.split(',')), default=set(), help="Experimental flags")
        s.add_argument("--epr-edges", dest="epr_edges", type=epr_edges, default=[], help="Experimental flags")
        s.add_argument("--log-dir", dest="log_dir", type=str, default="", help="Log directory")
        s.add_argument("--index", dest="log_dir", type=int, default=-1, help="Invariant index")
        s.add_argument("--inv", dest="log_dir", type=str, default="", help="Invariant name")

    return result