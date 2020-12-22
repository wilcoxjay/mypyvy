

from typing import Any, Callable, DefaultDict, Dict, Iterable, Sequence, TextIO, List, Optional, Set, Tuple, Union, cast, Counter as CounterType

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
import signal
import gc
from collections import Counter, defaultdict

import z3
from async_tools import AsyncConnection, ScopedProcess, ScopedTasks
from semantics import State
from translator import Z3Translator
import utils
from logic import Diagram, Expr, Solver, Trace
import syntax
from syntax import BinaryExpr, DefinitionDecl, IfThenElse, Let, NaryExpr, New, Not, QuantifierExpr, Scope, UnaryExpr
from fol_trans import eval_predicate, formula_to_predicate, predicate_to_formula, prog_to_sig, state_to_model
from separators import Constraint, Neg, Pos, Imp
from separators.separate import FixedImplicationSeparator, Logic, PrefixConstraints, PrefixSolver

async def _robust_check(base_formula: Callable[[Solver, Z3Translator], None], formulas: Sequence[Callable[[Solver, Z3Translator], None]], n_states: int = 1, parallelism: int = 1, timeout: float = 0.0, log: TextIO = sys.stdout, prefix: str = '') -> Union[Trace, z3.CheckSatResult]:
    def _luby(i: int) -> int:
        x = i + 1
        if (x+1) & x == 0:
            return (x+1)//2
        low = 2**(x.bit_length()-1) # largest power of two not exceeding x
        return _luby(x-low)

    _params = [(f_i, use_cvc4) for use_cvc4 in [True, False] for f_i in range(len(formulas))]
    _next_index: Dict[Tuple[int, bool], int] = dict((k, 0) for k in _params)
    _total_time: float = 0
    _time_spent: Dict[Tuple[int, bool], float] = dict((k, 0.0) for k in _params)
    formulas_unsat: Set[int] = set()
    
    def get_timeout(k: Tuple[int, bool], index: int) -> float:
        (f_i, use_cvc4) = k
        if use_cvc4:
            return 0.5 * 2**index + index * 0.5
        else:
            return 0.2 if index == 0 else 0.5 if index == 1 else 1.5 * _luby(index - 2)
            
    def get_next() -> Optional[Tuple[int, int, bool, float]]:
        nonlocal _total_time
        if timeout > 0 and _total_time >= timeout:
            return None
        choices = [(t, (f_i, use_cvc4)) for (f_i, use_cvc4), t in _time_spent.items() if f_i not in formulas_unsat]
        if len(choices) == 0:
            return None
        (_, k) = min(choices)
        index = _next_index[k]
        to = get_timeout(k, index)
        if timeout > 0 and _total_time + to > timeout:
            to = max(min(0.1, timeout - _total_time), to)
        _next_index[k] += 1
        _time_spent[k] += to
        _total_time += to

        return (k[0], index, k[1], to)

    result: asyncio.Future[Union[Trace, z3.CheckSatResult]] = asyncio.Future()

    async def _robust_check_worker(conn: AsyncConnection) -> None:
        s_z3 = Solver(use_cvc4=False)
        s_cvc4 = Solver(use_cvc4=True)
        t = s_z3.get_translator(n_states)
        base_formula(s_z3, t)
        base_formula(s_cvc4, t)
        while True:
            try:
                (f_i, count, use_cvc4, time_limit) = cast(Tuple[int, int, bool, float], await conn.recv())
            except EOFError:
                return
            s = s_cvc4 if use_cvc4 else s_z3
            with s.new_frame():
                formulas[f_i](s, t)
                print(f"{prefix} _robust_check(): checking ({f_i}, {count}, {use_cvc4}) in {time_limit}", file=log, flush=True)
                # print(s.assertions())
                r = s.check(timeout = min(1000000000, int(time_limit * 1000)))
                print(f"{prefix} _robust_check(): r = {r}", file=log, flush=True)
                if not use_cvc4 and r == z3.sat:
                    print(f"{prefix} _robust_check(): transmuting z3 sat->unknown", file=log, flush=True)
                    r = z3.unknown
                tr = Z3Translator.model_to_trace(s.model(minimize=True), n_states) if r == z3.sat else r
            await conn.send(tr)
    
    _running: int = parallelism
    async def _manager() -> None:
        nonlocal _running
        with ScopedProcess(_robust_check_worker) as conn:
            while True:
                v = get_next()
                if v is None:
                    _running -= 1
                    if not result.done():
                        if len(formulas_unsat) == len(formulas):
                            result.set_result(z3.unsat)
                        elif _running == 0:
                            result.set_result(z3.unknown)
                    return
                await conn.send(v)
                start = time.time()
                r = await conn.recv()
                end = time.time()
                print(f"{prefix} _robust_check(): query {v} returned {z3.sat if isinstance(r, Trace) else r} in {end-start:0.3f}", file=log, flush=True)
                if r == z3.unsat:
                    formulas_unsat.add(v[0])
                elif isinstance(r, Trace):
                    if not result.done():
                        result.set_result(r)
                    return

    async with ScopedTasks() as tasks:
        for _ in range(parallelism):
            tasks.add(_manager())
        return await result


async def robust_check_transition(old_hyps: Iterable[Expr], new_conc: Expr, minimize: Optional[bool] = None, transition: Optional[DefinitionDecl] = None, parallelism:int = 1, timeout: float = 0.0, log: TextIO = sys.stdout) -> Union[Trace, z3.CheckSatResult]:
    prefix = "/tmp"#  if utils.args.log_dir == "" else utils.args.log_dir
    id = f'{random.randint(0,1000000000-1):09}'
    file = os.path.join(prefix, f"query-{id}.pickle")
    with open(file, 'wb') as f:
        pickle.dump((old_hyps, new_conc, minimize, transition.name if transition is not None else None), f, protocol=pickle.HIGHEST_PROTOCOL)
    def rb_log(*args: Any) -> None:
        print(f'[Rb-{id}]', *args, file=log, flush=True)

    try:
        start = time.time()
        def base_formula(s: Solver, t: Z3Translator) -> None:
            pass
        def make_formula(s: Solver, t: Z3Translator, prog_scope: Scope, transition: DefinitionDecl) -> None:
            for e in [New(Not(new_conc)), transition.as_twostate_formula(prog_scope)]:
                s.add(t.translate_expr(e))
            exprs = list(old_hyps)
            random.shuffle(exprs)
            for e in exprs:
                s.add(t.translate_expr(e))
        formulas = [(lambda s, t, trans=transition: make_formula(s, t, syntax.the_program.scope, trans)) for transition in syntax.the_program.transitions()]
        
        return await _robust_check(base_formula, formulas, 2, parallelism=parallelism, timeout=timeout, log=log, prefix=f'[Rb-{id}]')
    finally:
        elapsed = time.time() - start
        rb_log(f"query took {elapsed:0.3f}")
        if elapsed < 5:
            os.remove(file)
        else:
            os.rename(file, os.path.join(prefix, f"hard-query-{int(elapsed):04d}-{id}.pickle"))

async def robust_check_implication(hyps: Iterable[Expr], conc: Expr, minimize: Optional[bool] = None, parallelism:int = 1, timeout: float = 0.0, log: TextIO = sys.stdout) -> Optional[Trace]:
    id = f'{random.randint(0,1000000000-1):09}'
    def rb_log(*args: Any) -> None:
        print(f'[RI-{id}]', *args, file=log, flush=True)

    try:
        start = time.time()
        def base_formula(s: Solver, t: Z3Translator) -> None:
            pass
        def make_formula(s: Solver, t: Z3Translator) -> None:
            for h in hyps:
                s.add(t.translate_expr(h))
            s.add(t.translate_expr(Not(conc)))
        r = await _robust_check(base_formula, [make_formula], 1, parallelism=parallelism, timeout=timeout, log=log, prefix=f'[RI-{id}]')
        return r if isinstance(r, Trace) else None
    finally:
        elapsed = time.time() - start
        rb_log(f"query took {elapsed:0.3f}")


async def IG_query_summary(x: TextIO, s: 'ParallelFolIc3', frame: int, state: int, rationale: str, smt_log: TextIO) -> Optional[Expr]:
    print(f"Inductive generalize blocking {state} in frame {frame} for {rationale}", file=x)
    st = s._states[state]
    size_summary = ', '.join(f"|{sort.name}|={len(elems)}" for sort, elems in st.univs.items())
    print(f"Size of state to block {size_summary}", file=x)
    # golden: List[Formula] = []
    f: Optional[Expr] = None
    for inv in syntax.the_program.invs():
        if s._states[state].eval(inv.expr) == False:
            cex = await robust_check_transition([*(s._predicates[j] for j in s.frame_predicates(frame-1)), inv.expr], inv.expr, minimize=False, log=smt_log)
            print("Possible formula is:", inv.expr, '(relatively inductive)' if cex is None else '(not relatively inductive)', file=x)
            if cex is None:
                f = inv.expr
    return f

def satisifies_constraint(c: Constraint, p: Expr, states: Union[Dict[int, State], List[State]]) -> bool:
    if isinstance(c, Pos):
        if not states[c.i].eval(p):
            return False
    elif isinstance(c, Neg):
        if states[c.i].eval(p):
            return False
    elif isinstance(c, Imp):
        if states[c.i].eval(p) and not states[c.j].eval(p):
            return False
    return True


class ParallelFolIc3(object):
    FrameNum = Optional[int]
    def __init__(self) -> None:
        self._sig = prog_to_sig(syntax.the_program, two_state=False)

        self._states: List[State] = [] # List of discovered states (excluding some internal cex edges)
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
        self._smt_log: TextIO = sys.stdout if utils.args.log_dir == '' else open(os.path.join(utils.args.log_dir, 'smt.log'), 'w')
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
    def add_state(self, s: State) -> int:
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
            cex = await robust_check_transition(list(self._predicates[j] for j in fp), p, minimize='no-minimize-block' not in utils.args.expt_flags, parallelism=10, log=self._smt_log)
            if fp != set(self.frame_predicates(i)):
                # Set of predicates changed across the await call. To avoid breaking the meta-invariant, loop around for another iteration
                made_changes = True
                continue
            if cex == z3.unsat:
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
            elif isinstance(cex, Trace):
                # Add the blocker and the sucessor state. We need the successor state because
                # if we show the blocker is reachable, it is actually the successor that invalidates
                # the predicate and is required to mark it as bad
                blocker = self.add_state(cex.as_state(0))
                blocker_successor = self.add_state(cex.as_state(1))
                self.add_transition(blocker, blocker_successor)

                self._pushing_blocker[index] = blocker
                # Signal here so that heuristic tasks waiting on a pushing_blocker can be woken
                self._event_frames.set()
                self._event_frames.clear()
            else:
                print(f"cex {cex}")
                assert False
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

    async def push_all(self) -> None:
        async with self._push_pull_lock:
            start = time.time()
            while True:
                pushed = await self.push_once()
                made_infinite = self.check_for_f_infinity()
                # We did something, so go see if more can happen
                if pushed or made_infinite:
                    continue
                break
            print(f"Pushing completed in {time.time() - start:0.3f}sec")

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

    async def IG2_worker(self, conn: AsyncConnection) -> None:
        prog = syntax.the_program
        sep = FixedImplicationSeparator(self._sig, (), PrefixConstraints(), 0, set(), [])
        constraints: List[Constraint] = []
        sep_constraints: Set[Constraint] = set()
        mapping: Dict[int, int] = {}
        states: Dict[int, State] = {}
        while True:
            v = await conn.recv()
            if 'prefix' in v:
                (prefix, pc) = v['prefix']
                del sep
                sep = FixedImplicationSeparator(self._sig, prefix, pc, 1, set(), [])
                sep_constraints = set()
                mapping = {}
            if 'constraints' in v:
                (cons, extra_states) = v['constraints']
                states.update((i, pickle.loads(p)) for i,p in extra_states.items())
                constraints = list(cons)
            # if 'force-constraints' in v:
            #     for c in v['force-constraints']:
            #         for s in c.states():
            #             if s not in mapping:
            #                 mapping[s] = sep.add_model(state_to_model(states[s]))
            #             sep.add_constraint(c.map(mapping))
            #             sep_constraints.add(c)
            if 'sep' in v:
                minimized = False
                while True:
                    sep_r = sep.separate(minimize=minimized)
                    if sep_r is None:
                        await conn.send({'unsep': sep_constraints})
                        break

                    with prog.scope.n_states(1):
                        p = formula_to_predicate(sep_r, prog.scope)
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
                            await conn.send({'candidate': p, 'constraints': [c for c in constraints if c in sep_constraints]})
                            break

    async def IG2_manager(self, frame: int, state: int, rationale: str, timeout_sec: float = -1) -> Optional[Expr]:

        # Logging
        identity = self._next_ig_query_index
        self._next_ig_query_index += 1
        def ig_print(*args: Any, end: str='\n') -> None:
            print(f"[{rationale[0].upper()}({identity})]", *args, file=self._ig_log, flush=True, end=end)

        # A list of states local to this IG query. All constraints are w.r.t. this list
        states: List[State] = []
        _states_pickled: List[bytes] = []
        def add_local_state(s: State) -> int:
            states.append(s)
            _states_pickled.append(pickle.dumps(s, pickle.HIGHEST_PROTOCOL))
            return len(states) - 1
        _local_eval_cache: Dict[Tuple[int, int], bool] = {}
        def local_eval(pred: int, local_state: int) -> bool:
            if (pred, local_state) not in _local_eval_cache:
                _local_eval_cache[(pred, local_state)] = eval_predicate(states[local_state], self._predicates[pred])
            return _local_eval_cache[(pred, local_state)]


        prefix_solver = PrefixSolver(self._sig)
        frame_preds = set(self.frame_predicates(frame-1))

        necessary_constraints: Set[Constraint] = set([Neg(add_local_state(self._states[state]))]) # This is just Neg(0), the state to block
        constraints_in_frame: Set[Constraint] = set(necessary_constraints) # This is all constraints that satisfy the prior frame
        unsep_constraints: Set[Constraint] = set(necessary_constraints) # Constraints that are part of some unsep core, eliminating some prefix(es)
        popularity: CounterType[Constraint] = Counter() # Constraints that have shown to be useful in unsep cores
        popularity_total = 0
        # Seed the popular constraints with known positive states
        for pos_state in self._initial_states | self._useful_reachable:
            c = Pos(add_local_state(self._states[pos_state]))
            constraints_in_frame.add(c)
            popularity[c] = 1
        for n in necessary_constraints:
            popularity[n] = 2
        MAX_POPULAR = 150

        solution: asyncio.Future[Optional[Expr]] = asyncio.Future()

        # def check_popular_constraints(satsifies: Set[Constraint], p: Expr) -> Optional[Constraint]:
        #     for c, cnt in popularity.most_common(MAX_POPULAR):
        #         if c in satsifies: continue # skip constraints we know p to satisfy
        #         if not satisifies_constraint(c, p, states):
        #             return c
        #     return None

        async def check_candidate(p: Expr) -> Union[Constraint, z3.CheckSatResult]:
            # F_0 => p?
            initial_state = await robust_check_implication([init.expr for init in syntax.the_program.inits()], p, minimize='no-minimize-cex' not in utils.args.expt_flags, log=self._smt_log)
            if initial_state is not None:
                ig_print("Adding initial state")
                return Pos(add_local_state(initial_state.as_state(0)))

            # F_i-1 ^ p => wp(p)?
            # start = time.time()
            edge = await robust_check_transition([p, *(self._predicates[fp] for fp in frame_preds)], p, minimize='no-minimize-cex' not in utils.args.expt_flags, parallelism = 2, timeout=120, log=self._smt_log)
            # ig_print(f"Check took {time.time()-start:0.3f}s {'unsat' if edge is None else 'sat'}")
            # if golden is not None and edge is not None:
            #     print(f"Golden {eval_predicate((edge, 0), golden)} -> {eval_predicate((edge, 1), golden)}")
            if isinstance(edge, Trace):
                ig_print(f"Adding edge")
                return Imp(add_local_state(edge.as_state(0)), add_local_state(edge.as_state(1)))
            elif edge == z3.unsat:
                return z3.unsat
            else:
                return z3.unknown

        async def worker_handler(pc: PrefixConstraints) -> None:
            nonlocal solution, popularity, popularity_total

            with ScopedProcess(self.IG2_worker) as conn:
                # Keep track of which states the worker knows about, so we only send necessary ones
                worker_known_states: Set[int] = set()
                def send_constraints(cs: List[Constraint]) -> Tuple[List[Constraint], Dict[int, bytes]]:
                    new_states = set(s for c in cs for s in c.states()).difference(worker_known_states)
                    extra_states = {i: _states_pickled[i] for i in new_states}
                    worker_known_states.update(new_states)
                    # print(f"Constraints are: {cs}")
                    return (cs, extra_states)

                while True:
                    # Get a prefix from the solver
                    # feasible = prefix_solver.is_feasible(unsep_constraints, ((True, 'inst'), (True, 'quorum'), (True, 'round'), (True, 'round'), (True, 'value'), (False, 'node')))
                    # ig_print(f"Is Feasible: {feasible}")
                    pre = prefix_solver.get_prefix(unsep_constraints, pc)
                    if pre is None:
                        return
                    pre_pp = ".".join(self._sig.sort_names[sort_i] for (_, sort_i) in pre)
                    ig_print(f"Trying: {pre_pp}")
                    reservation = prefix_solver.reserve(pre, pc)
                    await conn.send({'prefix': (pre, pc)})
                    pop = [c for c, cnt in popularity.most_common(MAX_POPULAR)]
                    last_sep_constraints : Set[Constraint] = set()
                    next_constraints = list(necessary_constraints) + pop
                    while True:
                        if solution.done(): return
                        await conn.send({'constraints': send_constraints(next_constraints), 'sep': None})
                        v = await conn.recv()
                        if 'candidate' in v:
                            p, sep_constraints = v['candidate'], v['constraints']
                            # new_constraint = check_popular_constraints(set(current_constraints), p)
                            # if new_constraint is not None:
                            #     ig_print("Using popular constraint")
                            #     current_constraints.append(new_constraint)
                            #     popularity[new_constraint] += 1
                            #     popularity_total += 1
                            #     if popularity_total == 2*MAX_POPULAR:
                            #         popularity_total = 0
                            #         for k in popularity.keys():
                            #             popularity[k] = (popularity[k] * 3) // 4
                            #     continue
                            set_sep_constraints = set(sep_constraints)
                            for cons in set_sep_constraints - last_sep_constraints:
                                if cons in necessary_constraints: continue
                                ig_print("Using popular constraint")
                                popularity[cons] += 1
                                popularity_total += 1
                                if popularity_total == 2*MAX_POPULAR:
                                    popularity_total = 0
                                    for k in popularity.keys():
                                        popularity[k] = (popularity[k] * 5) // 6
                            last_sep_constraints = set_sep_constraints

                            if len(last_sep_constraints) > 100:
                                new_constraint_result: Union[Constraint, z3.CheckSatResult] = z3.unknown
                                ig_print(f"Used more than 100 constraints")
                            else:
                                new_constraint_result = await check_candidate(p)
                                if new_constraint_result == z3.unknown:
                                    ig_print(f"Solver returned unknown")

                            if isinstance(new_constraint_result, Constraint):
                                # print(f"Adding {new_constraint}")
                                #current_constraints.append(new_constraint)
                                popularity[new_constraint_result] = popularity.most_common(MAX_POPULAR//2)[-1][1] + 1
                                popularity_total += 1
                                if popularity_total == 2*MAX_POPULAR:
                                    popularity_total = 0
                                    for k in popularity.keys():
                                        popularity[k] = (popularity[k] * 5) // 6
                                # if golden is not None:
                                #     if not satisifies_constraints([new_constraint], golden, states):
                                #         print(f"! -- oops {new_constraint} isn't satisfied by {golden}")

                                next_constraints = [new_constraint_result] + list(necessary_constraints) + [c for c, cnt in popularity.most_common(MAX_POPULAR)]
                                continue
                            elif new_constraint_result == z3.unsat:
                                if not solution.done():
                                    ig_print(f"SEP with |constr|={len(sep_constraints)}")
                                    ig_print(f"Learned {p}")
                                    solution.set_result(p)
                                return
                            elif new_constraint_result == z3.unknown:
                                core = sep_constraints
                                ig_print(f"UNKNOWN: {pre_pp} ({pc.logic}) with |core|={len(core)}")
                                prefix_solver.unsep(core, pc, pre)
                                unsep_constraints.update(core)
                                break    

                        elif 'unsep' in v:
                            core = v['unsep']
                            ig_print(f"UNSEP: {pre_pp} ({pc.logic}) with |core|={len(core)}")
                            # if False:
                            #     test_sep = FixedImplicationSeparator(sig, pre, pc)
                            #     m = {i: test_sep.add_model(state_to_model(states[i])) for i in range(len(states))}
                            #     for c in cs:
                            #         test_sep.add_constraint(c.map(m))
                            #     assert test_sep.separate() is None
                            prefix_solver.unsep(core, pc, pre)
                            # for c in core:
                            #     popularity[c] += 1
                            unsep_constraints.update(core)
                            break
                        else:
                            assert False
                    # print(f"Done with: {pre}")
                    prefix_solver.unreserve(reservation)

        async def frame_updater() -> None:
            nonlocal constraints_in_frame, frame_preds
            def in_frame(current_frame: Set[int], c: Constraint) -> bool:
                return not isinstance(c, Imp) or all(local_eval(fp, c.i) for fp in current_frame)
            while True:
                current_frame = set(self.frame_predicates(frame-1))
                if frame_preds != current_frame:
                    constraints_in_frame = set([c for c in constraints_in_frame if in_frame(current_frame, c)])
                    unsep_constraints.intersection_update(constraints_in_frame)
                    for c in list(popularity.keys()):
                        if c not in constraints_in_frame:
                            del popularity[c]
                    frame_preds = current_frame
                else:
                    await self._event_frames.wait()

        async def wait_blocked() -> None:
            while True:
                if not all(self.eval(pred, state) for pred in self.frame_predicates(frame)):
                    ig_print(f"State {state} in frame {frame} is blocked by concurrent update")
                    if not solution.done():
                        solution.set_result(None)
                    return
                await self._event_frames.wait()
        
        async def timeout() -> None:
            if timeout_sec < 0: return
            await asyncio.sleep(timeout_sec)
            if not solution.done():
                ig_print(f"State {state} in frame {frame} has timed out")
                solution.set_result(None)
            return
            
        async def summary_logger() -> None:
            t = io.StringIO()
            await IG_query_summary(t, self, frame, state, rationale, self._smt_log)
            ig_print(t.getvalue(), end='')

        async def logger() -> None:
            query_start = time.time()
            ig_print(f"started at: {query_start - self._start_time:0.2f}s")
            while True:
                try: await asyncio.sleep(30)
                except asyncio.CancelledError:
                    if solution.done():
                        ig_print(f"popularity: {popularity.most_common(MAX_POPULAR)}")
                    ig_print(f"finished in: {time.time() - query_start:0.2f}s")
                    raise
                ig_print(f"time: {time.time() - query_start:0.2f}s")

        if utils.args.logic == 'universal':
            pcs = [PrefixConstraints(Logic.Universal),
                   PrefixConstraints(Logic.Universal, max_repeated_sorts = 2),
                   PrefixConstraints(Logic.Universal, max_repeated_sorts = 2, min_depth=4),
                   PrefixConstraints(Logic.Universal, max_repeated_sorts = 2, min_depth=6),
                   PrefixConstraints(Logic.Universal, max_repeated_sorts = 3, min_depth=7)]
        elif utils.args.logic == 'epr':
            pcs = [PrefixConstraints(Logic.Universal, max_repeated_sorts=2, max_depth=6),
                   PrefixConstraints(Logic.Universal, max_repeated_sorts=3, max_depth=6),
                   PrefixConstraints(Logic.EPR, max_alt=1, max_repeated_sorts=2, max_depth=6),
                   PrefixConstraints(Logic.EPR, max_alt=2, max_repeated_sorts=3, max_depth=6),
                   PrefixConstraints(Logic.EPR, min_depth=5, max_alt=1, max_repeated_sorts=2, max_depth=6),
                   PrefixConstraints(Logic.EPR, min_depth=5, max_alt=2, max_repeated_sorts=3, max_depth=6)]
            # pcs = [PrefixConstraints(Logic.EPR, min_depth=6, max_alt=2, max_repeated_sorts=2)]
        elif utils.args.logic == 'fol':
            pcs = [PrefixConstraints(Logic.FOL),
                   PrefixConstraints(Logic.FOL, max_repeated_sorts = 2),
                   PrefixConstraints(Logic.FOL, max_repeated_sorts = 2, min_depth=4),
                   PrefixConstraints(Logic.FOL, max_repeated_sorts = 2, min_depth=5)]
        else:
            assert False
        for pc in pcs:
            if pc.logic == Logic.EPR:
                qe = [(self._sig.sort_indices[x], self._sig.sort_indices[y])
                      for (x,y) in itertools.product(self._sig.sort_names, self._sig.sort_names)
                      if (x,y) not in utils.args.epr_edges]
                pc.disallowed_quantifier_edges = qe
        multiplier = 4

        async with ScopedTasks() as tasks:
            tasks.add(*(worker_handler(pc) for pc in pcs * multiplier))
            tasks.add(frame_updater())
            tasks.add(logger())
            tasks.add(summary_logger())
            tasks.add(wait_blocked())
            tasks.add(timeout())
            s = await solution
            ig_print("Exiting IG_manager")
            return s

    async def parallel_inductive_generalize(self, frame: int, state: int, rationale: str = '') -> None:
        # Force a GC cycle so forked processes are as light as possible
        gc.collect()
        p = await self.IG2_manager(frame, state, rationale, timeout_sec=20*60 if rationale == 'heuristic-push' else -1)
        if p is None or any(not self.eval(pred, state) for pred in self.frame_predicates(frame)):
            print(f"State {state} was blocked in frame {frame} by concurrent task")
            return

        print(f"Learned new predicate {p} blocking {state} in frame {frame} for {rationale}")
        self.add_predicate(p, frame)
        await self.push_all()
        self.print_predicates()
        # print(f"Done with parallel_inductive_generalize2 for blocking {state} in frame {frame} for {rationale}")

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
        formula_to_block = syntax.Not(s.as_onestate_formula()) \
                        if utils.args.logic != "universal" else \
                        syntax.Not(Diagram(s).to_ast())
        # We do this in a loop to ensure that if someone concurrently modifies the frames, we still compute a correct
        # predecessor.
        while True:
            fp = set(self.frame_predicates(frame-1))
            # edge = check_transition(self._solver, [self._predicates[i] for i in self.frame_predicates(frame-1)], formula_to_block, minimize=False)
            edge = await robust_check_transition([self._predicates[i] for i in fp], formula_to_block, minimize='no-minimize-block' not in utils.args.expt_flags, parallelism=2, log=self._smt_log)
            if fp != set(self.frame_predicates(frame-1)):
                continue
            break
        if isinstance(edge, Trace):
            pred = self.add_state(edge.as_state(0))
            self.add_transition(pred, state)
            self._predecessor_cache[key] = pred
            return pred
        elif edge == z3.unsat:
            self._no_predecessors[state] = fp
            return None
        else:
            assert False       

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
            st = self._states[new_r]
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
            await self.parallel_inductive_generalize(frame, state, rationale=rationale)
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
                    await self.push_all()
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
        while True:
            for safety in sorted(self._safeties, key = lambda x: ParallelFolIc3.frame_key(self._frame_numbers[x])):
                fn = self._frame_numbers[safety]
                # This is called after push, so if either of these is not satisfied we should have exited
                if fn is None:
                    continue
                if safety not in self._pushing_blocker:
                    print(f"Cannot learn because pushing not yet complete")
                    await self.push_all()
                    break
                blocker = self._pushing_blocker[safety]
                # print(f"Blocking {blocker} in frame {fn} for learning")
                await self.block(fn, blocker, "learning")
                break
            else:
                return

    async def run(self) -> None:
        self._start_time = time.time()
        self.init()
        await self.push_all()
        self.print_predicates()
        async with ScopedTasks() as tasks:
            # if 'no-heuristic-pushing' not in utils.args.expt_flags:
            #     tasks.add(self.heuristic_pushing_to_the_top_worker(True))
            #     tasks.add(self.heuristic_pushing_to_the_top_worker(True))
            tasks.add(self.inexpensive_reachability())
            tasks.add(self.learn())
            while not self.is_complete():
                await self._event_frames.wait()

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
    # Redirect stdout if we have a log directory
    if utils.args.log_dir:
        os.makedirs(utils.args.log_dir, exist_ok=True)
        sys.stdout = io.TextIOWrapper(open(os.path.join(utils.args.log_dir, "main.log"), "wb"), line_buffering=False, encoding='utf8')

    # Print initial header with command line and git hash
    print(f"ParallelFolIc3 log for {os.path.basename(utils.args.filename)}")
    print(f"Command line: {' '.join(sys.argv)}")
    try:
        path = os.path.dirname(os.path.realpath(__file__))
        wd = os.getcwd() if path == '' else path
        print(f"git commit: {subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=wd, encoding='utf8').strip()}")
    except (subprocess.CalledProcessError, FileNotFoundError):
        print(f"git commit: unknown")

    async def main() -> None:
        # We need to do this inside a function so that the asyncio objects in the constructor of
        # p use the same event loop as p.run()
        def print_tasks(a: Any, b: Any) -> None:
            tasks = asyncio.all_tasks(asyncio.get_running_loop())
            print("Tasks: ")
            for task in tasks:
                print("Task:", task)
                print("  Coro:", task.get_coro())
                print("  Stack:", task.get_stack())
                print("")
            print("End of tasks.", flush=True)
        signal.signal(signal.SIGUSR1, print_tasks)
        # asyncio.get_event_loop().set_debug(True)
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
    # if utils.args.logic == 'epr':
        # graph = prog.decls_quantifier_alternation_graph([x.expr for x in prog.invs()] + [syntax.Not(x.expr) for x in prog.invs()])
        # print(f"Is acyclic: {networkx.is_directed_acyclic_graph(graph)}")
        # arg = ','.join(f'{a}->{b}' for (a,b) in graph.edges)
        # print(f"--epr-edges='{arg}'")

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

def _check_core_unsat_times(transition: DefinitionDecl, core: List[Expr], new_conc: Expr, use_cvc4: bool) -> None:
    for i in range(10):
        s = Solver(use_cvc4=use_cvc4)
        t = s.get_translator(2)
        s.add(t.translate_expr(New(Not(new_conc))))
        s.add(t.translate_expr(transition.as_twostate_formula(syntax.the_program.scope)))
        s.z3solver.set('seed', random.randint(1,2**64-1))
        s.z3solver.set('ctrl_c', False)
        for c in core:
            s.add(t.translate_expr(c))
        start = time.time()
        r = s.check(timeout=100000)
        print(f'{r} {time.time()-start:0.3f}')
            

def _minimize_unsat_core(transition: DefinitionDecl, core: List[Expr], new_conc: Expr) -> None:
    s = Solver()
    t = s.get_translator(2)
    s.add(t.translate_expr(New(Not(new_conc))))
    s.add(t.translate_expr(transition.as_twostate_formula(syntax.the_program.scope)))
    s.z3solver.set('seed', random.randint(1,2**64-1))
    s.z3solver.set('ctrl_c', False)
    final_core = core[:0]
    T = 1000
    while len(core) > 0:
        with s.new_frame():
            for c in final_core + core[1:]:
                s.add(t.translate_expr(c))
            r = s.check(timeout=T)
            print(f'final_core={len(final_core)} rest={len(core)} res={r}')
            if r == z3.unknown:
                T = T + 1000
                continue
            if r == z3.unsat:
                pass
            else:
                final_core = final_core + [core[0]]
            core = core[1:]
            T = 1000
    print(f"minimized core has size {len(final_core)}")
    for f in final_core:
        print(f'  {f}')
    print("With z3:")
    _check_core_unsat_times(transition, final_core, new_conc, False)
    print("With cvc4:")
    _check_core_unsat_times(transition, final_core, new_conc, True)
    
def _find_unsat_core(transition: DefinitionDecl, old_hyps: List[Expr], new_conc: Expr) -> None:
    s = Solver()
    s.z3solver.set('seed', random.randint(1,2**64-1))
    s.z3solver.set('ctrl_c', False)
    t = s.get_translator(2)
    s.add(t.translate_expr(New(Not(new_conc))))
    s.add(t.translate_expr(transition.as_twostate_formula(syntax.the_program.scope)))
    
    current_core: List[Expr] = []
    all_hyps = list(old_hyps)
    start = time.time()
    current_core = list(all_hyps[:1])
    T = 1000
    while True:
        with s.new_frame():
            for c in current_core:
                s.add(t.translate_expr(c))
            print(f'{len(current_core)} {T}')
            r = s.check(timeout=T)
            print(r)
            if r == z3.unsat:
                print(f'found core in {time.time()-start}sec ({len(current_core)})')
                _minimize_unsat_core(transition, current_core, new_conc)
                return
            if r == z3.unknown:
                T = T + 1000
                if len(current_core) > 0:
                    random.shuffle(current_core)
                    current_core = current_core[:-1]
            if r == z3.sat:
                T = max(100, (T * 3)//4)
                random.shuffle(all_hyps)
                for e in all_hyps:
                    if e in current_core: continue
                    current_core.append(e)
                    break

    print("UNKNOWN??")

def fol_benchmark_solver(_: Solver) -> None:
    if utils.args.output:
        sys.stdout = open(utils.args.output, "w")
    print(f"Benchmarking {utils.args.query} ({utils.args.filename})")
    (old_hyps, new_conc, minimize, transition_name) = cast(Tuple[List[Expr], Expr, Optional[bool], Optional[str]], pickle.load(open(utils.args.query, 'rb')))
    if True:
        start = time.time()
        r = asyncio.run(robust_check_transition(old_hyps, new_conc, parallelism=2, timeout=100))
        print(f"overall: {z3.sat if isinstance(r, Trace) else r} in {time.time() - start:0.3f}")
        
    if True:
        def base_formula(s: Solver, t: Z3Translator) -> None:
            pass
        def make_formula(s: Solver, t: Z3Translator, prog_scope: Scope, transition: DefinitionDecl) -> None:
            for e in [New(Not(new_conc)), transition.as_twostate_formula(prog_scope)]:
                s.add(t.translate_expr(e))
            exprs = list(old_hyps)
            # random.shuffle(exprs)
            for e in exprs:
                s.add(t.translate_expr(e))
            
        formulas = [(lambda s, t, trans=transition: make_formula(s, t, syntax.the_program.scope, trans)) for transition in syntax.the_program.transitions()]
        start = time.time()
        r = asyncio.run(_robust_check(base_formula, formulas, 2, parallelism=2, timeout=100, prefix='[CTX]'))
        print(f"overall: {z3.sat if isinstance(r, Trace) else r} in {time.time() - start:0.3f}")
        
    if False:
        print("Trying basic tests...")
        longest = max(*(len(t.name) for t in syntax.the_program.transitions()))
        for s in [Solver(use_cvc4=False), Solver(use_cvc4=True)]:
            print("Solver: cvc4" if s.use_cvc4 else "Solver: z3")
            # if not s.use_cvc4:
            #     s.z3solver.set(':mbqi', True)
            t = s.get_translator(2)
            for transition in syntax.the_program.transitions():
                with s.new_frame():
                    print(f"checking {transition.name: <{longest}}... ", end='', flush=True)
                    start = time.time()
                    for h in old_hyps:
                        s.add(t.translate_expr(h))
                    s.add(t.translate_expr(New(Not(new_conc))))
                    s.add(t.translate_expr(transition.as_twostate_formula(syntax.the_program.scope)))
                    res = s.check(timeout=10000)
                    end = time.time()
                    print(f"{str(res): <7} {end-start:0.3f}")
    # tr = next(t for t in syntax.the_program.transitions() if t.name == 'receive_join_acks')

    # _find_unsat_core(tr, old_hyps, new_conc)
    # print("Original timings")
    # print("With z3:")
    # _check_core_unsat_times(tr, old_hyps, new_conc, False)
    # print("With cvc4:")
    # _check_core_unsat_times(tr, old_hyps, new_conc, True)
    if False:
        print("Trying multi tests...")
        longest = max(*(len(t.name) for t in syntax.the_program.transitions()))
        for transition in syntax.the_program.transitions():
            for i in range(10):
                s = Solver()
                s.z3solver.set('seed', random.randint(1,2**64-1))
                t = s.get_translator(2)
                print(f"checking {transition.name: <{longest}}... ", end='', flush=True)
                start = time.time()
                for h in old_hyps:
                    s.add(t.translate_expr(h))
                s.add(t.translate_expr(New(Not(new_conc))))
                s.add(t.translate_expr(transition.as_twostate_formula(syntax.the_program.scope)))
                res = s.check(timeout=30000)
                end = time.time()
                print(f"{str(res): <7} {end-start:0.3f}")

    if False:
        start = time.time()
        r = asyncio.run(robust_check_transition(old_hyps, new_conc))
        end = time.time()
        print(f"robust_check_transition: {'UNSAT' if r is None else 'SAT'} in {end-start:0.3f}")

def epr_edges(s: str) -> List[Tuple[str, str]]:
    r = []
    for pair in s.split(','):
        if pair.split() == '': continue
        parts = pair.split("->")
        if len(parts) != 2:
            raise ValueError("Epr edges must be of the form sort->sort, sort2 -> sort3, ...")
        r.append((parts[0].strip(), parts[1].strip()))
    return r

def add_argparsers(subparsers: argparse._SubParsersAction) -> Iterable[argparse.ArgumentParser]:
    result : List[argparse.ArgumentParser] = []

    s = subparsers.add_parser('p-fol-ic3', help='Run parallel IC3 inference with folseparators')
    s.set_defaults(main=p_fol_ic3)
    s.add_argument("--logic", choices=('fol', 'epr', 'universal'), default="fol", help="Restrict form of separators to given logic (fol is unrestricted)")
    s.add_argument("--epr-edges", dest="epr_edges", type=epr_edges, default=[], help="Experimental flags")
    s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: set(x.split(',')), default=set(), help="Experimental flags")
    s.add_argument("--log-dir", dest="log_dir", type=str, default="", help="Log directory")
    result.append(s)

    s = subparsers.add_parser('fol-extract', help='Extract conjuncts to a file')
    s.set_defaults(main=fol_extract)
    s.add_argument("--logic", choices=('fol', 'epr', 'universal'), default="fol", help="Restrict form of separators to given logic (fol is unrestricted)")
    result.append(s)

    s = subparsers.add_parser('fol-learn', help='Learn a given formula')
    s.set_defaults(main=fol_learn)
    s.add_argument("--logic", choices=('fol', 'epr', 'universal'), default="fol", help="Restrict form of separators to given logic (fol is unrestricted)")
    s.add_argument("--index", dest="index", type=int, default=-1, help="Invariant index")
    s.add_argument("--inv", dest="inv", type=str, default="", help="Invariant name")
    result.append(s)

    s = subparsers.add_parser('fol-benchmark-solver', help='Test SMT solver backend')
    s.set_defaults(main=fol_benchmark_solver)
    s.add_argument("--query", type=str, help="Query to benchmark")
    s.add_argument("--output", type=str, help="Output to file")
    result.append(s)

    return result
