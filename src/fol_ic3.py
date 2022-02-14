
from typing import Any, BinaryIO, DefaultDict, Dict, Iterable, Iterator, Sequence, TextIO, List, Optional, Set, Tuple, Union, cast

import argparse
import sys
import os
import random
import time
import io
import pickle
import asyncio
import itertools
import signal
import tempfile

from dataclasses import dataclass
from collections import defaultdict

from trace_tools import Tracer, load_trace, trace
from async_tools import AsyncConnection, FileDescriptor, ScopedProcess, ScopedTasks, get_forkserver
from robust_check import AdvancedChecker, ClassicChecker, RobustChecker
from semantics import State
import utils
from logic import Diagram, Expr, Solver, Trace
import syntax
from syntax import AppExpr, BinaryExpr, DefinitionDecl, IfThenElse, InvariantDecl, Let, NaryExpr, New, Not, Program, QuantifierExpr, Scope, TraceDecl, UnaryExpr
from fol_trans import eval_predicate, formula_to_predicate, predicate_to_formula, prog_to_sig, state_to_model

try:
    from separators.logic import Signature
    from separators import Constraint, Neg, Pos, Imp
    from separators.separate import FixedImplicationSeparatorPyCryptoSat, FixedImplicationSeparatorPyCryptoSatCNF, Logic, PrefixConstraints, Separator
except ModuleNotFoundError:
    pass

import networkx
import z3
from solver_cvc5 import SatResult

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

class Logging:
    def __init__(self, log_dir: str) -> None:
        self._log_dir = log_dir
        supress_logs = True
        self._sep_log: TextIO = open('/dev/null', 'w') if log_dir == '' or supress_logs else open(os.path.join(utils.args.log_dir, 'sep.log'), 'w', buffering=1)
        self._smt_log: TextIO = open('/dev/null', 'w') if log_dir == '' or supress_logs else open(os.path.join(utils.args.log_dir, 'smt.log'), 'w', buffering=1)
        self._ig_log: TextIO = sys.stdout if log_dir == '' else open(os.path.join(utils.args.log_dir, 'ig.log'), 'w', buffering=1)
        self._lemmas_log: BinaryIO = open('/dev/null' if log_dir == '' else os.path.join(utils.args.log_dir, 'lemmas.pickle'), 'wb')
        self._frames_log: BinaryIO = open('/dev/null' if log_dir == '' else os.path.join(utils.args.log_dir, 'frames.pickle'), 'wb')
        self._ig_queries_log: BinaryIO = open('/dev/null' if log_dir == '' else os.path.join(utils.args.log_dir, 'ig-queries.pickle'), 'wb')
        self._ig_queries_pickler: pickle.Pickler = pickle.Pickler(self._ig_queries_log, protocol=pickle.HIGHEST_PROTOCOL)

async def _main_IG2_worker(conn: AsyncConnection, sig: Signature, log: FileDescriptor) -> None:
    sys.stdout = os.fdopen(log.id, 'w')
    sys.stdout.reconfigure(line_buffering=True)
    print("Started Worker")
    prog = syntax.the_program
    sep: Separator = cast(Separator, None)
    label = '[?]'
    sep_pc = PrefixConstraints()
    if utils.args.logic == 'epr':
        sep_pc.logic = Logic.EPR
        qe = [(sig.sort_indices[x], sig.sort_indices[y])
              for (x, y) in itertools.product(sig.sort_names, sig.sort_names)
              if (x, y) not in utils.args.epr_edges]
        sep_pc.disallowed_quantifier_edges = qe
    else:
        sep_pc.logic = Logic.FOL

    constraints: List[Constraint] = []
    sep_constraints: Set[Constraint] = set()
    sep_constraints_order: List[Constraint] = []
    mapping: Dict[int, int] = {}
    states: Dict[int, State] = {}
    prefix: Tuple[Tuple[Optional[bool], int], ...] = ()
    sep_time, eval_time = 0.0, 0.0
    while True:
        v = await conn.recv()
        if 'prefix' in v:
            prefix, k_cubes, expt_flags, label = v['prefix'], v['k_cubes'], v['expt_flags'], v['label']
            del sep
            if 'sep-cnf' not in utils.args.expt_flags:
                sep = FixedImplicationSeparatorPyCryptoSat(sig, prefix, pc=sep_pc, k_cubes=k_cubes, expt_flags=expt_flags, debug=False)
            else:
                sep = FixedImplicationSeparatorPyCryptoSatCNF(sig, prefix, pc=sep_pc, k_cubes=k_cubes, expt_flags=expt_flags, debug=False)
            sep_constraints = set()
            sep_constraints_order = []
            mapping = {}
            sep_time, eval_time = 0.0, 0.0
        if 'constraints' in v:
            (cons, extra_states) = v['constraints']
            states.update((i, pickle.loads(p)) for i, p in extra_states.items())
            constraints = list(cons)
        if 'block_last_separator' in v:
            sep.block_last_separator()
        if 'sep' in v:
            minimized_reset_value = 'always-minimize-sep' in utils.args.expt_flags
            minimized = minimized_reset_value
            while True:
                print(label, f"Separating with prefix {prefix}")
                start = time.perf_counter()
                sep_r = sep.separate(minimize=minimized)
                sep_time += time.perf_counter() - start
                if sep_r is None:
                    print(label, f"UNSEP |core|={len(sep_constraints)} in (sep {sep_time:0.3f}, eval {eval_time:0.3f})")
                    await conn.send({'unsep': True, 'constraints': sep_constraints_order, 'times': (sep_time, eval_time)})
                    break

                with prog.scope.n_states(1):
                    p = formula_to_predicate(sep_r, prog.scope)
                print(label, f"Internal candidate: {p}")
                start = time.perf_counter()
                evaled_constraints = []
                for c in constraints:
                    if c in sep_constraints: continue
                    if not satisifies_constraint(c, p, states):
                        print(label, f"Adding internal constraint {c}")
                        for s in c.states():
                            if s not in mapping:
                                mapping[s] = sep.add_model(state_to_model(states[s]))
                        sep.add_constraint(c.map(mapping))
                        sep_constraints.add(c)
                        sep_constraints_order.append(c)
                        minimized = minimized_reset_value
                        eval_time += time.perf_counter() - start
                        break
                    else:
                        evaled_constraints.append(c)
                else:
                    eval_time += time.perf_counter() - start
                    # All known constraints are satisfied
                    if not minimized:
                        minimized = True
                        continue  # continue the loop, now asking for a minimized separator
                    else:
                        print(label, f"Satisfied with {p} in (sep {sep_time:0.3f}, eval {eval_time:0.3f})")
                        await conn.send({'candidate': p, 'constraints': sep_constraints_order, 'times': (sep_time, eval_time)})
                        break
                this_eval_time = time.perf_counter() - start
                if 'log-long-eval' in utils.args.expt_flags and this_eval_time > 0.1:
                    with tempfile.NamedTemporaryFile(prefix='eval-', suffix='.pickle', dir=os.path.join(utils.args.log_dir, 'eval'), delete=False) as temp:
                        states_to_save = {}
                        for c in evaled_constraints:
                            if c in sep_constraints: continue
                            for s in c.states():
                                if s not in states_to_save:
                                    states_to_save[s] = states[s]
                        pickle.dump((states_to_save, p), temp)



@dataclass(eq=True, frozen=True)
class Prefix:
    # __slots__= ['quant_blocks', 'begin_forall']
    quant_blocks: Tuple[Tuple[int, ...], ...]
    begin_forall: bool

    def depth(self) -> int: return sum(sum(block) for block in self.quant_blocks)
    def alternations(self) -> int: return max(1, len(self.quant_blocks)) - 1
    def linearize(self) -> Tuple[Tuple[bool, int], ...]:
        is_forall = self.begin_forall
        quants = []
        for block in self.quant_blocks:
            for sort, count in enumerate(block):
                for _ in range(count):
                    quants.append((is_forall, sort))
            is_forall = not is_forall
        return tuple(quants)

def generate_exclusive(sorts: int, depth: int, alts: int, repeat: int, existentials: bool) -> Iterator[Prefix]:
    def _repeat_of(b: Tuple[Tuple[int, ...], ...], sorts: int = sorts) -> int:
        counts = [0 for s in range(sorts)]
        for block in b:
            for i in range(sorts):
                counts[i] += block[i]
        return max(counts)
    def _blocks(sorts_allowance: Tuple[int, ...], size: int) -> Iterator[Tuple[int, ...]]:
        assert size >= 0
        if len(sorts_allowance) == 0:
            if size == 0:
                yield ()
            # if size > 0, don't yield anything
            return
        for count_of_first in reversed(range(min(sorts_allowance[0], size)+1)):
            # print('trying', sorts_allowance, size, count_of_first)
            for rest in _blocks(sorts_allowance[1:], size-count_of_first):
                yield (count_of_first, *rest)
    def _gen(sorts_allowance: Tuple[int, ...], depth: int, alts: int, ifa: bool, depth_e: int) -> Iterator[Tuple[Tuple[int, ...], ...]]:
        if alts == 0:
            if not ifa and depth_e != depth: return # at the last existential block, but we don't have
            if ifa and depth_e != 0: return
            for b in _blocks(sorts_allowance, depth):
                yield (b,)
        if depth == 0:
            return # alts > 0 but depth = 0, infeasible

        for quants_in_first in (reversed(range(1, depth)) if ifa else range(1, min(depth, depth_e+1))):
            for first_block in _blocks(sorts_allowance, quants_in_first):
                remaining_allowance = tuple(a - b for a,b in zip(sorts_allowance, first_block))
                rem_depth_e = (depth_e - quants_in_first) if not ifa else depth_e
                for rest in _gen(remaining_allowance, depth - quants_in_first, alts - 1, not ifa, rem_depth_e):
                    yield (first_block, *rest)

    for depth_e in range(0, depth + 1):
        for b in _gen(tuple(min(repeat, depth) for _ in range(sorts)), depth, alts, True, depth_e):
            if _repeat_of(b) == repeat:
                yield Prefix(b, True)
    if not existentials: return
    for depth_e in range(0, depth + 1):
        for b in _gen(tuple(min(repeat, depth) for _ in range(sorts)), depth, alts, False, depth_e):
            if _repeat_of(b) == repeat:
                yield Prefix(b, False)

def subprefixes(p: Prefix) -> Sequence[Prefix]:
    sub_p = []
    for i, block in enumerate(p.quant_blocks):
        total_quants = sum(block)
        for sort, count in enumerate(block):
            if count > 0 and (i == 0 or i == len(p.quant_blocks)-1 or total_quants > 1):
                sub_p.append(Prefix((*p.quant_blocks[:i], (*block[:sort], count-1, *block[sort+1:]), *p.quant_blocks[i+1:]),
                                    not p.begin_forall if i == 0 and total_quants == 1 else p.begin_forall))
    return sub_p

class PrefixQueue:
    def __init__(self, sig: Signature, logic: Logic, skip_prefixes: bool):
        self._sig =  sig
        self._prefix_generators: Dict[Tuple[int, int, int], Iterator[Prefix]] = {} # maps (depth, alts, max_repeats) to a prefix generator

        if 'no-prefix-restrictions' not in utils.args.expt_flags:
            # Prefix restrictions
            if logic == Logic.Universal:
                pcs = [
                    PrefixConstraints(Logic.Universal),
                    PrefixConstraints(Logic.Universal, max_repeated_sorts=2)]
            elif logic == Logic.EPR:
                pcs = [
                    PrefixConstraints(Logic.Universal),
                    PrefixConstraints(Logic.Universal, max_repeated_sorts=2),
                    PrefixConstraints(Logic.EPR, max_alt=1, max_repeated_sorts=1),
                    PrefixConstraints(Logic.EPR, max_alt=1, max_repeated_sorts=2),
                    PrefixConstraints(Logic.EPR, max_alt=2, max_repeated_sorts=2),
                    PrefixConstraints(Logic.EPR, max_alt=2)]
            elif logic == Logic.FOL:
                pcs = [
                    PrefixConstraints(Logic.Universal),
                    PrefixConstraints(Logic.Universal, max_repeated_sorts=2),
                    PrefixConstraints(Logic.FOL, max_alt=1, max_repeated_sorts=1),
                    PrefixConstraints(Logic.FOL, max_alt=1, max_repeated_sorts=2),
                    PrefixConstraints(Logic.FOL, max_alt=2, max_repeated_sorts=2),
                    PrefixConstraints(Logic.FOL, max_alt=2)]
            else:
                assert False
        else:
            # No prefix restrictions
            if logic == Logic.Universal:
                pcs = [PrefixConstraints(Logic.Universal)]
            elif logic == Logic.EPR:
                pcs = [PrefixConstraints(Logic.EPR)]
            elif logic == Logic.FOL:
                pcs = [PrefixConstraints(Logic.FOL)]
            else:
                assert False
        for _pc in pcs:
            if _pc.logic == Logic.EPR:
                qe = [(self._sig.sort_indices[x], self._sig.sort_indices[y])
                      for (x,y) in itertools.product(self._sig.sort_names, self._sig.sort_names)
                      if (x,y) not in utils.args.epr_edges]
                _pc.disallowed_quantifier_edges = qe


        self._skip_prefixes = skip_prefixes
        self._pcs = pcs
        self._pcs_stopped = [False] * len(self._pcs)
        self._pcs_worked_on = [0] * len(self._pcs)
        self._outstanding: Dict[Prefix, int] = {}
        self._front_of_queue: List[Tuple[Prefix, int]] = []

        # Logging
        self._total_skipped_prefixes = 0
        self._total_prefixes_considered = 0

    def _get_prefix_generator(self, pc: PrefixConstraints) -> Iterator[Iterator[Prefix]]:
        alts = 0 if pc.logic == Logic.Universal else pc.max_alt + 1
        for d in range(10):
            for alt in [0] if alts == 0 else range(1, min(d, alts)):
                for max_r in range(1, min(d, pc.max_repeated_sorts)+1):
                    if (d, alt, max_r) not in self._prefix_generators:
                        # print(f"Starting {d} {alt}")
                        self._prefix_generators[(d, alt, max_r)] = generate_exclusive(len(self._sig.sorts), d, alt, max_r, alt > 0)
                    yield self._prefix_generators[(d, alt, max_r)]

    def satisfies_epr(self, pc: PrefixConstraints, p: Prefix) -> bool:
        if pc.logic != Logic.EPR: return True
        for q_a, q_b in itertools.combinations(p.linearize(), 2):
            if q_a[0] != q_b[0] and (q_a[1], q_b[1]) in pc.disallowed_quantifier_edges:
                # print(f"Failed {q_a} {q_b}")
                return False
        return True

    def get_prefix(self) -> Tuple[Prefix, int]:

        if len(self._front_of_queue) > 0:
            (p, pc_index) = self._front_of_queue.pop()
            self._outstanding[p] = pc_index
            return p, pc_index

        while True:
            possiblities = [(i, count) for (i, count) in enumerate(self._pcs_worked_on) if not self._pcs_stopped[i]]
            random.shuffle(possiblities) # fairly divide up effort when there are more threads than pcs
            if len(possiblities) == 0: raise StopIteration
            pc_index, _ = min(possiblities, key = lambda x: x[1])
            self._pcs_worked_on[pc_index] += 1
            pc = self._pcs[pc_index]

            while True:
                try:
                    candidate = next(itertools.chain.from_iterable(self._get_prefix_generator(pc)))
                except StopIteration:
                    self._pcs_stopped[pc_index] = True
                    break
                if self._skip_prefixes and not self.satisfies_epr(pc, candidate):
                    #self._print("Skipping", " ".join(('A' if fa == True else 'E' if fa == False else 'Q') + self._sig.sort_names[sort_i] + '.' for (fa, sort_i) in candidate.linearize()))
                    self._total_skipped_prefixes += 1
                    continue
                self._total_prefixes_considered += 1
                self._outstanding[candidate] = pc_index
                return candidate, pc_index


    # Return a prefix to the front of the queue. Used to support resuming after a successful separation with new constraints
    def return_prefix(self, p: Prefix) -> None:
        assert p in self._outstanding
        pcs_index = self._outstanding[p]
        self._pcs_worked_on[pcs_index] -= 1
        self._front_of_queue.append((p, pcs_index))
        del self._outstanding[p]

    # Complete a prefix, used when it is found UNSEP
    def complete_prefix(self, p: Prefix) -> None:
        assert p in self._outstanding
        self._pcs_worked_on[self._outstanding[p]] -= 1
        del self._outstanding[p]

class IGSolver:
    def __init__(self, state: State, positive: List[State], frame: List[Expr], logs: Logging, prog: Program, rationale: str, identity: int, prior_solver: Optional['IGSolver'] = None):
        self._sig = prog_to_sig(prog)
        self._logs = logs

        # Logging
        self._rationale = rationale
        self._identity = identity
        self._log_prefix = f"[{rationale[0].upper()}({identity})]"
        self._solve_index = 0
        self._total_constraints_found: int = 0
        self._total_prefixes_considered: int = 0
        self._total_skipped_prefixes: int = 0
        self._smt_timeout = 300.0

        # A list of states local to this IG query. All constraints are w.r.t. this list
        self._states: List[State] = []
        self._states_pickled_cache: List[bytes] = []

        # self._local_eval_cache: Dict[Tuple[int, int], bool] = {} # maps (predicate, state) to evaluation result

        self._frame = frame

        self._necessary_constraints: Set[Constraint] = set([Neg(self.add_local_state(state))]) # This is just Neg(0), the state to block
        self._reachable_constraints: Set[Constraint] = set([Pos(self.add_local_state(st)) for st in positive])

        # Prefix handling
        # self._max_repeats = 3

        self._prefix_queue = PrefixQueue(self._sig, Logic.from_str(utils.args.logic), 'no-skip-epr-prefixes' not in utils.args.expt_flags)
        self._unsep_cores: Dict[Prefix, List[Constraint]] = {}

        self._previous_unsep_cores: Dict[Prefix, List[Constraint]] = {} if prior_solver is None else prior_solver._unsep_cores
        self._previous_states = [] if prior_solver is None else prior_solver._states
        self._previous_to_current_states: Dict[int, int] = {}
        self._constraints_mapping: Dict[Constraint, Optional[Constraint]] = {}
        self._previous_constraints: Set[Constraint] = set()


    def _print(self, *args: Any, end: str='\n') -> None:
        print(self._log_prefix, *args, file=self._logs._ig_log, end=end)

    def add_local_state(self, s: State) -> int:
        self._states.append(s)
        self._states_pickled_cache.append(pickle.dumps(s, pickle.HIGHEST_PROTOCOL))
        return len(self._states) - 1


    async def check_candidate(self, checker: RobustChecker, p: Expr, span: Tracer.Span) -> Union[Constraint, SatResult]:
        # F_0 => p?
        with span.span('SMT-init') as s:
            initial_state = await checker.check_implication([init.expr for init in syntax.the_program.inits()], p, parallelism=1, timeout=self._smt_timeout)
            s.data(result=initial_state.result)
        if initial_state.result == SatResult.sat and isinstance(initial_state.trace, Trace):
            self._print("Adding initial state")
            return Pos(self.add_local_state(initial_state.trace.as_state(0)))
        elif initial_state.result == SatResult.unknown:
            self._print("Warning, implication query returned unknown")

        # F_i-1 ^ p => wp(p)?
        with span.span('SMT-tr') as s:
            edge = await checker.check_transition([p, *self._frame], p, parallelism=1, timeout=self._smt_timeout)
            s.data(result=edge.result)
        if edge.result == SatResult.sat and isinstance(edge.trace, Trace):
            self._print(f"Adding edge")
            return Imp(self.add_local_state(edge.trace.as_state(0)), self.add_local_state(edge.trace.as_state(1)))
        return SatResult.unsat if edge.result == SatResult.unsat and initial_state.result == SatResult.unsat else SatResult.unknown


    def make_constraint_current(self, c: Constraint) -> Optional[Constraint]:
        if isinstance(c, Neg): return None
        if isinstance(c, Pos):
            if c not in self._constraints_mapping:

                if c.i not in self._previous_to_current_states:
                    self._previous_to_current_states[c.i] = self.add_local_state(self._previous_states[c.i])
                nc = Pos(self._previous_to_current_states[c.i])
                self._constraints_mapping[c] = nc
                self._previous_constraints.add(nc)
            return self._constraints_mapping[c]
        if isinstance(c, Imp):
            if c not in self._constraints_mapping:
                pre_state = self._previous_states[c.i]
                if all(pre_state.eval(f) for f in self._frame):
                    if c.i not in self._previous_to_current_states:
                        self._previous_to_current_states[c.i] = self.add_local_state(self._previous_states[c.i])
                    if c.j not in self._previous_to_current_states:
                        self._previous_to_current_states[c.j] = self.add_local_state(self._previous_states[c.j])
                    nci = Imp(self._previous_to_current_states[c.i], self._previous_to_current_states[c.j])
                    self._constraints_mapping[c] = nci
                    self._previous_constraints.add(nci)
                else:
                    self._constraints_mapping[c] = None
            return self._constraints_mapping[c]
        assert False

    def add_to_frame(self, f: Expr) -> None:
        self._frame.append(f)
        # TODO: invalidate all -> constraints that don't have pre-states satisfying f, and rework those predicates that are no longer unsep

    def add_negative_state(self, s: State) -> None:
        i = self.add_local_state(s)
        self._necessary_constraints.add(Neg(i))

    async def solve(self, n_threads: int = 1, timeout: Optional[float] = None, span: Tracer.Span = Tracer.dummy_span()) -> Optional[Expr]:
        solution: asyncio.Future[Optional[Expr]] = asyncio.Future()
        self._solve_index += 1

        async def worker_controller() -> None:
            worker_known_states: Set[int] = set()
            worker_prefix_sent = False
            checker: RobustChecker = AdvancedChecker(syntax.the_program, self._logs._smt_log) # if 'no-advanced-checker' not in utils.args.expt_flags else ClassicChecker(self._logs._smt_log)

            def send_constraints(cs: List[Constraint]) -> Tuple[List[Constraint], Dict[int, bytes]]:
                new_states = set(s for c in cs for s in c.states()).difference(worker_known_states)
                extra_states = {i: self._states_pickled_cache[i] for i in new_states}
                worker_known_states.update(new_states)
                return (cs, extra_states)

            def predict_useful_constraints(prefix: Prefix, previous_useful: Sequence[Constraint]) -> List[Constraint]:
                cores: List[List[Optional[Constraint]]] = [list(previous_useful)]
                if prefix in self._previous_unsep_cores:
                    core = [self.make_constraint_current(c) for c in self._previous_unsep_cores[prefix]]
                    cores.append([c for c in core if c is not None])
                for sub_p in subprefixes(prefix):
                    if sub_p in self._unsep_cores:
                        sub_core: List[Optional[Constraint]] = list(reversed(self._unsep_cores[sub_p]))
                        #sub_core.sort(key = lambda x: not isinstance(x, Pos))
                        cores.append(sub_core)
                #print(f"cores: {cores}")
                cores.append([None, None, None, *(x for x in self._reachable_constraints)])
                random.shuffle(cores)

                return [x for x in itertools.chain.from_iterable(itertools.zip_longest(*cores)) if x is not None]

            with ScopedProcess(get_forkserver(), _main_IG2_worker, self._sig, FileDescriptor(self._logs._sep_log.fileno())) as conn:
                # Loop over prefixes
                while True:
                    # get a prefix.
                    try:
                        prefix, pcs_index = self._prefix_queue.get_prefix()
                    except StopIteration:
                        self._print("Stopping worker")
                        return
                    with span.span("Pre") as prefix_span:
                        try:
                            pre_pp = " ".join(('A' if fa == True else 'E' if fa == False else 'Q') + self._sig.sort_names[sort_i] + '.' for (fa, sort_i) in prefix.linearize())
                            k_cubes = 3 if any(not fa for (fa, _) in prefix.linearize()) else 1
                            debug_this_process = False # pre_pp == 'Aquorum. Around. Around. Avalue. Avalue. Enode.'
                            prefix_span.data(prefix=prefix, category=pcs_index)

                            n_discovered_constraints = 0
                            # start a separator instance
                            worker_prefix_sent = False

                            if prefix in self._unsep_cores:
                                previous_solve_constraints: List[Constraint] = list(self._unsep_cores[prefix])
                            else:
                                previous_solve_constraints = []

                            next_constraints = list(self._necessary_constraints) + predict_useful_constraints(prefix, previous_solve_constraints)

                            start_time = time.perf_counter()
                            self._print(f"Trying: {pre_pp}")
                            # Loop for adding constraints for a particular prefix
                            while True:
                                if solution.done():
                                    self._print("Solution is .done(), exiting")
                                    return
                                with prefix_span.span('Sep') as sep_span:
                                    await conn.send({'constraints': send_constraints(next_constraints), 'sep': None,
                                                    **({'prefix': prefix.linearize(), 'k_cubes': k_cubes, 'expt_flags': utils.args.expt_flags, 'label': self._log_prefix} if not worker_prefix_sent else {})})
                                    worker_prefix_sent = True
                                    # if not logged_problem and time.perf_counter() - start_time > 5:
                                    #     _log_sep_problem(log_name, prefix.linearize(), next_constraints, self._states, self._frame)
                                    #     logged_problem = True
                                    if debug_this_process:
                                            self._print(f"Separating")

                                    v = await conn.recv()
                                if 'candidate' in v:
                                    p, sep_constraints, (time_sep, time_eval) = cast(Expr, v['candidate']), cast(List[Constraint], v['constraints']), cast(Tuple[float, float], v['times'])
                                    sep_span.data(core=len(sep_constraints), time_sep=time_sep, time_eval=time_eval)
                                    self._unsep_cores[prefix] = sep_constraints # share our constraints with others that may be running
                                    if debug_this_process:
                                        self._print(f"Checking {p}")
                                    start = time.perf_counter()
                                    new_constraint_result = await self.check_candidate(checker, p, prefix_span)

                                    if debug_this_process:
                                        self._print(f"Received unsat? {new_constraint_result == SatResult.unsat} sat? {isinstance(new_constraint_result, Constraint)}")
                                    if new_constraint_result == SatResult.unknown:
                                        self._print(f"Solver returned unknown ({p})")
                                        await conn.send({'block_last_separator': None})
                                        continue
                                    if isinstance(new_constraint_result, Constraint):
                                        next_constraints = [new_constraint_result, *self._necessary_constraints, *predict_useful_constraints(prefix, previous_solve_constraints)]
                                        self._total_constraints_found += 1
                                        n_discovered_constraints += 1
                                        if debug_this_process:
                                            self._print(f"Discovered: {len(sep_constraints)}/{n_discovered_constraints} in {time.perf_counter() - start}")
                                        continue
                                    elif new_constraint_result == SatResult.unsat:
                                        if not solution.done():
                                            # if utils.args.log_dir != '':
                                            #     states_needed = set(s for c in sep_constraints for s in c.states())
                                            #     structs = dict((i, s) for i, s in enumerate(self._states) if i in states_needed)
                                            #     with open(os.path.join(utils.args.log_dir, f'ig-solutions/ig-solution-{self._log_prefix}.pickle'), 'wb') as output:
                                            #         pickle.dump({'states': structs, 'constraints': sep_constraints, 'solution': p, 'prior_frame': self._frame}, output)

                                            self._prefix_queue.return_prefix(prefix)
                                            t = time.perf_counter() - start_time
                                            previous_constraints_used = len([c for c in sep_constraints if c in self._previous_constraints])
                                            self._print(f"SEP: {pre_pp} with core={len(sep_constraints)} ({n_discovered_constraints} novel, {previous_constraints_used} prev) time {t:0.3f} (sep {time_sep:0.3f}, eval {time_eval:0.3f})")
                                            self._print(f"Learned {p}")
                                            if utils.args.log_dir != '':
                                                with open(os.path.join(utils.args.log_dir, f'smt-queries/sep-prefix-{self._log_prefix}-{self._solve_index}.pickle'), 'wb') as output:
                                                    pickler = pickle.Pickler(output, protocol=pickle.HIGHEST_PROTOCOL)
                                                    for q in checker._all_queries:
                                                        pickler.dump(q)
                                            prefix_span.data(sep=True)
                                            solution.set_result(p)
                                        return
                                    assert False

                                elif 'unsep' in v:
                                    core: List[Constraint] = v['constraints']
                                    (time_sep, time_eval) = cast(Tuple[float, float], v['times'])
                                    sep_span.data(core=len(core), time_sep=time_sep, time_eval=time_eval)
                                    t = time.perf_counter() - start_time
                                    previous_constraints_used = len([c for c in core if c in self._previous_constraints])
                                    extra = ""
                                    self._print(f"UNSEP: {pre_pp} with core={len(core)} ({n_discovered_constraints} novel, {previous_constraints_used} prev) time {t:0.3f} (sep {time_sep:0.3f}, eval {time_eval:0.3f}){extra}")
                                    self._unsep_cores[prefix] = core
                                    self._prefix_queue.complete_prefix(prefix)
                                    prefix_span.data(unsep=True)
                                    break
                                else:
                                    assert False
                        except asyncio.CancelledError:
                            self._prefix_queue.return_prefix(prefix)
                            prefix_span.data(cancelled=True)
                            raise

        async def logger() -> None:
            query_start = time.perf_counter()
            self._print(f"Starting IG query with timeout {timeout}")
            try:
                while True:
                    await asyncio.sleep(30)
                    self._print(f"time: {time.perf_counter() - query_start:0.3f} sec constraints: {self._total_constraints_found} prefixes: {self._total_prefixes_considered} epr-skipped: {self._total_skipped_prefixes}")
            finally:
                self._print(f"finished in: {time.perf_counter() - query_start:0.3f} sec",
                            f"constraints: {self._total_constraints_found} prefixes: {self._total_prefixes_considered} epr-skipped: {self._total_skipped_prefixes}",
                            f"({'cancelled' if solution.cancelled() else 'done'})")

        async with ScopedTasks() as tasks:
            tasks.add(logger())
            tasks.add(*(worker_controller() for _ in range(n_threads)))
            try:
                s = await asyncio.wait_for(solution, timeout)
            except asyncio.TimeoutError:
                self._print("IG query timed out")
                s = None
            self._print("Exiting IG_manager")
            return s
@dataclass
class Blocker:
    state: int = -1 # State that needs to be blocked
    frame: int = -1 # Frame to block in
    lemma: int = -1 # If a lemma push blocker, the lemma that was pushed
    successor: int = -1 # If a predecessor blocker, the state in the next frame it is a predecessor of
    type_is_predecessor: bool = False # If False, a lemma push blocker. If True, a predecessor blocker


class IC3Frames:
    FrameNum = Optional[int]
    def __init__(self, logs: Logging, span: Tracer.Span, parallelism: int = 1) -> None:
        self._states: List[State] = [] # List of discovered states (excluding some internal cex edges)
        self._initial_states: Set[int] = set() # States satisfying the initial conditions
        self._transitions: Set[Tuple[int, int]] = set() # Set of transitions between states (s,t)
        self._successors: DefaultDict[int, Set[int]] = defaultdict(set) # Successors t of s in s -> t
        self._predecessors: DefaultDict[int, Set[int]] = defaultdict(set) # Predecessors s of t in s -> t
        self._reachable: Dict[int, int] = dict() # Known reachable states (not necessarily including initial states)
        self._useful_reachable: Set[int] = set() # Known reachable states that violate some lemma

        self._lemmas: List[Expr] = [] # List of predicates discovered
        self._frame_numbers: List[Optional[int]] = [] # the frame number for each lemma
        self._initial_conditions: Set[int] = set() # predicates that are initial conditions in F_0
        self._safeties: Set[int] = set() # predicates that are safety properties

        self._eval_cache: Dict[Tuple[int, int], bool] = {} # Record eval for a (lemma, state)
        self._immediate_pushing_blocker: Dict[int, int] = {} # State for a lemma in F_i that prevents it pushing to F_i+1
        self._ultimate_pushing_blocker: Dict[int, Optional[Blocker]] = {} # (State, Frame) that prevents the lemma from pushing (may be an ancestor of the immediate pushing blocker, None if can't be pushed)
        self._former_pushing_blockers: DefaultDict[int, Dict[int, None]] = defaultdict(dict) # Pushing blockers from prior frames
        self._predecessor_cache: Dict[Tuple[int, int], int] = {} # For (F_i, state) gives s such that s -> state is an edge and s in F_i
        self._no_predecessors: Dict[int, Set[int]] = {} # Gives the set of predicates that block all predecessors of a state
        self._bad_lemmas: Dict[int, int] = dict() # Predicates that violate a known reachable state
        self._pushability_unknown_lemmas: Set[int] = set() # Predicates that violate a known reachable state
        self._redundant_lemmas: Set[int] = set() # Predicates that are implied by the conjunction of non-redundant F_inf lemmas


        self._push_lock = asyncio.Lock()
        self._event_frame_update = asyncio.Event()
        self._logs = logs
        self._span = span
        self._pushing_parallelism = parallelism
        self._pushing_timeout = 300.0

        self._push_robust_checkers: Dict[int, RobustChecker] = {}
        self._predecessor_robust_checker: RobustChecker = AdvancedChecker(syntax.the_program, self._logs._smt_log) if 'no-advanced-checker' not in utils.args.expt_flags else ClassicChecker(self._logs._smt_log)
        self._redundancy_checker: RobustChecker = AdvancedChecker(syntax.the_program, self._logs._smt_log) if 'no-advanced-checker' not in utils.args.expt_flags else ClassicChecker(self._logs._smt_log)


    # Frame number manipulations (make None === infinity)
    @staticmethod
    def frame_max(a: FrameNum, b: FrameNum) -> FrameNum:
        if a is None or b is None: return None
        return max(a, b)
    @staticmethod
    def frame_leq(a: FrameNum, b: FrameNum) -> bool:
        if b is None: return True
        if a is None: return False
        return a <= b
    @staticmethod
    def frame_key(a: FrameNum) -> Tuple[int, int]:
        if a is None: return (1, 0)
        return (0, a)


    # Adding and manipulating states, transitions, and predicates
    async def add_lemma(self, p: Expr, frame: int = 0) -> int:
        async with self._push_lock:
            i = len(self._lemmas)
            self._lemmas.append(p)
            self._frame_numbers.append(frame)
            self._logs._lemmas_log.write(pickle.dumps({i: p}))
            self._logs._lemmas_log.flush()
            return i
    async def add_state(self, s: State) -> int:
        i = len(self._states)
        self._states.append(s)
        # print(f"State {i} is {s[0].as_state(s[1])}")
        return i
    async def add_transition(self, a: int, b: int) -> None:
        if (a, b) in self._transitions:
            return
        self._transitions.add((a, b))
        self._predecessors[b].add(a)
        self._successors[a].add(b)
        # Warning: this method does not compute new reachability. In all current uses, the
        # state a is a new state that cannot be known to be reachable, so this is safe.
        # If a method of determing new transitions between existing states is added, it must
        # call push_reachable to update reachability information.

    # Evaluation and contents of frames
    def eval(self, lemm: int, state: int) -> bool:
        if (lemm, state) not in self._eval_cache:
            self._eval_cache[(lemm, state)] = eval_predicate(self._states[state], self._lemmas[lemm])
        return self._eval_cache[(lemm, state)]
    def frame_lemmas(self, i: FrameNum) -> Iterable[int]:
        yield from (index for index, f in enumerate(self._frame_numbers) if IC3Frames.frame_leq(i, f) and index not in self._redundant_lemmas)
    def frame_transitions(self, i: FrameNum) -> Iterable[Tuple[int, int]]:
        yield from ((a, b) for a, b in self._transitions if all(self.eval(p, a) for p in self.frame_lemmas(i)))

    def print_lemmas(self) -> None:
        print("[IC3] ---- Frame summary")
        # cnt = len([i for (i,fn) in enumerate(self._frame_numbers) if fn == 0 and i in self._bad_predicates])
        # print(f"[IC3] lemma  0 b ... (x{cnt})")
        for i, p, index in sorted(zip(self._frame_numbers, self._lemmas, range(len(self._lemmas))), key=lambda x: IC3Frames.frame_key(x[0])):
            code = '$' if index in self._safeties else \
                   'i' if index in self._initial_conditions else \
                   'B' if index in self._bad_lemmas and IC3Frames.frame_leq(self._bad_lemmas[index], i) else \
                   'u' if index in self._pushability_unknown_lemmas else \
                   'r' if index in self._redundant_lemmas else \
                   'b' if index in self._bad_lemmas else ' '
            fn_str = f"{i:2}" if i is not None else ' +'
            print(f"[IC3] lemma {fn_str} {code} {p}")
        print(f"[IC3] Reachable states: {len(self._reachable)} ({len(self._useful_reachable)} useful), initial states: {len(self._initial_states)}")
        print("[IC3] ----")
    def log_frames(self, elapsed: Optional[float] = None) -> None:
        data = {"frame_numbers": self._frame_numbers,
                "safeties": self._safeties,
                "initial_conditions": self._initial_conditions,
                "bad_lemmas": self._bad_lemmas,
                "redundant_lemmas": self._redundant_lemmas,
                "pushability_unknown_lemmas": self._pushability_unknown_lemmas,
                "elapsed": elapsed}
        self._logs._frames_log.write(pickle.dumps(data))
        self._logs._frames_log.flush()

    async def _get_predecessor(self, frame: int, state: int) -> Optional[int]:
        assert frame != 0
        key = (frame-1, state)
        if state in self._no_predecessors:
            if self._no_predecessors[state].issubset(self.frame_lemmas(frame - 1)):
                return None
            # If we are not a subset of the current frame, then we might have predecessors
            del self._no_predecessors[state]
        if key in self._predecessor_cache:
            pred = self._predecessor_cache[key]
            if all(self.eval(p, pred) for p in self.frame_lemmas(frame - 1)):
                return pred
            del self._predecessor_cache[key]

        # First, look for any known predecessors of the state
        for pred in self._predecessors[state]:
            if all(self.eval(p, pred) for p in self.frame_lemmas(frame - 1)):
                self._predecessor_cache[key] = pred
                return pred

        # We need to check for a predecessor
        s = self._states[state]
        formula_to_block = syntax.Not(s.as_onestate_formula() if utils.args.logic != "universal" else Diagram(s).to_ast())
        # We do this in a loop to ensure that if someone concurrently modifies the frames, we still compute a correct
        # predecessor. This is only currently used to ensure that speculative_push() doesn't need to synchronize with push()
        while True:
            fp = set(self.frame_lemmas(frame-1))
            # edge = check_transition(self._solver, [self._predicates[i] for i in self.frame_predicates(frame-1)], formula_to_block, minimize=False)
            #edge = await robust_check_transition([self._predicates[i] for i in fp], formula_to_block, minimize='no-minimize-block' not in utils.args.expt_flags, parallelism=2, log=self._logs._smt_log)
            edge = await self._predecessor_robust_checker.check_transition([self._lemmas[i] for i in fp], formula_to_block, parallelism=self._pushing_parallelism)
            if fp != set(self.frame_lemmas(frame-1)):
                continue
            break
        if isinstance(edge.trace, Trace):
            pred = await self.add_state(edge.trace.as_state(0))
            await self.add_transition(pred, state)
            self._predecessor_cache[key] = pred
            return pred
        elif edge.result == SatResult.unsat:
            self._no_predecessors[state] = fp
            return None
        else:
            assert False

    @staticmethod
    def _set_min(d: dict, index: Any, v: Any) -> bool:
        """Set d[index] = min(d[index], v), including when index is not in d. Returns True if a change was made."""
        if index in d and d[index] <= v:
                return False
        d[index] = v
        return True

    def _saturate_reachability(self, state:int, frame: int) -> None:
        # Mark state reachable
        if state in self._reachable and self._reachable[state] <= frame:
            return
        IC3Frames._set_min(self._reachable, state, frame)
        # self._reachable[state] = min(self._reachable.get(state, frame), frame)
        _reachable_worklist = set([state])

        while len(_reachable_worklist) > 0:
            item = _reachable_worklist.pop()
            assert item in self._reachable
            base_frame = self._reachable[item]
            for b in self._successors[item]:
                if IC3Frames._set_min(self._reachable, b, base_frame + 1):
                    _reachable_worklist.add(b)
                # if b not in self._reachable or self._reachable[b] > base_frame + 1:
                #     _reachable_worklist.add(b)
                # self._reachable[b] = min(self._reachable.get(b, base_frame + 1), base_frame + 1)
        

    def _mark_reachable_and_bad(self, state: int) -> None:
        initial_reachable = set(self._reachable.keys())
        self._saturate_reachability(state, 0)
        new = set(self._reachable.keys()) - initial_reachable
        if len(new) == 0:
            return
        print(f"Now have {len(self._reachable)} reachable states")
        # Mark any predicates as bad that don't satisfy all the reachable states
        for new_r in new:
            print(f"New reachable state: {new_r}")
            st = self._states[new_r]
            f = self._reachable[new_r] - 1 # frame before the frame that it is known reachable in
            for index, p in enumerate(self._lemmas):
                if not st.eval(p):
                    if IC3Frames._set_min(self._bad_lemmas, index, f):
                        print(f"Marked {p} as bad in frame {f}")
                        self._useful_reachable.add(new_r)

    async def _blockable_state(self, blocker: Blocker) -> Optional[Blocker]:
        if blocker.frame == 0:
            assert all(self.eval(i, blocker.state) for i in self._initial_conditions)
            self._mark_reachable_and_bad(blocker.state)
            return None
        pred = await self._get_predecessor(blocker.frame, blocker.state)
        if pred is None:
            return blocker
        else:
            new_blocker = Blocker(state=pred, frame = blocker.frame - 1, successor=blocker.state, type_is_predecessor=True)
            return await self._blockable_state(new_blocker)

    def _is_bad_lemma(self, lemm: int) -> bool:
        return (lemm in self._bad_lemmas and IC3Frames.frame_leq(self._bad_lemmas[lemm], self._frame_numbers[lemm]))

    async def _push_lemma(self, index: int, span: Tracer.Span) -> None:
        p, i = self._lemmas[index], self._frame_numbers[index]
        assert self._push_lock.locked()

        # No need to push things already in F_inf or bad lemmas
        if i is None or self._is_bad_lemma(index) or index in self._pushability_unknown_lemmas:
            return
        with span.span("PushLemma") as span:
            span.data(lemma=index)
            with span.span("ImBlocker"):
                if index in self._immediate_pushing_blocker:
                    blocker = self._immediate_pushing_blocker[index]
                    # Check if blocking state is reachable (thus we should never push)
                    if blocker in self._reachable:
                        assert index in self._bad_lemmas
                        return
                    # Check if the blocker state is still in F_i
                    if all(self.eval(lemma, blocker) for lemma in self.frame_lemmas(i)):
                        blocker_data = Blocker(state=blocker, frame=i, lemma=index, type_is_predecessor=False)
                        self._ultimate_pushing_blocker[index] = await self._blockable_state(blocker_data)
                        return
                    # The blocker is invalidated
                    self._former_pushing_blockers[index][self._immediate_pushing_blocker[index]] = None
                    del self._immediate_pushing_blocker[index]


            # Either there is no known blocker or it was just invalidated by some new lemma in F_i
            # First check if any former blockers still work
            with span.span("Former"):
                for former_blocker in reversed(self._former_pushing_blockers[index].keys()):
                    if all(self.eval(lemma, former_blocker) for lemma in self.frame_lemmas(i)):
                        print(f"Using former blocker {former_blocker}")
                        self._immediate_pushing_blocker[index] = former_blocker
                        blocker_data = Blocker(state=former_blocker, frame=i, lemma=index, type_is_predecessor=False)
                        self._ultimate_pushing_blocker[index] = await self._blockable_state(blocker_data)
                # We found a former one to use
                if index in self._immediate_pushing_blocker:
                    return


            # Check if any new blocker exists
            with span.span("SMTpush") as smt_span:
                if index not in self._push_robust_checkers:
                    self._push_robust_checkers[index] = AdvancedChecker(syntax.the_program, self._logs._smt_log) if 'no-advanced-checker' not in utils.args.expt_flags else ClassicChecker(self._logs._smt_log)

                fp = set(self.frame_lemmas(i))
                time_limit = 0.0 if index in self._safeties else self._pushing_timeout
                cex = await self._push_robust_checkers[index].check_transition(list(self._lemmas[j] for j in fp), p, parallelism=self._pushing_parallelism, timeout=time_limit)
                assert fp == set(self.frame_lemmas(i))

                if cex.result == SatResult.unsat:
                    print(f"Pushed {'lemma' if index not in self._safeties else 'safety'} to frame {i+1}: {p} (core size: {len(cex.core)}/{len(fp)})")
                    smt_span.data(pushed=True)
                    self._frame_numbers[index] = i + 1
                    self._event_frame_update.set()
                    self._event_frame_update.clear()
                    return
                elif cex.result == SatResult.sat and isinstance(cex.trace, Trace):
                    trace = cex.trace
                    # Add the blocker and the sucessor state. We need the successor state because
                    # if we show the blocker is reachable, it is actually the successor that invalidates
                    # the lemma and is required to mark it as bad
                    blocker = await self.add_state(trace.as_state(0))
                    blocker_successor = await self.add_state(trace.as_state(1))
                    await self.add_transition(blocker, blocker_successor)

                    self._immediate_pushing_blocker[index] = blocker
                    blocker_data = Blocker(state=blocker, frame=i, lemma=index, type_is_predecessor=False)
                    self._ultimate_pushing_blocker[index] = await self._blockable_state(blocker_data)
                    # Signal here so that heuristic tasks waiting on a pushing_blocker can be woken
                    self._event_frame_update.set()
                    self._event_frame_update.clear()
                    return
                elif index not in self._safeties and cex.result == SatResult.unknown:
                    print(f"Pushability unknown: {p}")
                    self._pushability_unknown_lemmas.add(index)
                    return
                else:
                    print(f"cex {cex.result}")
                    assert False

    async def _check_f_inf_redundancy(self, push_span: Tracer.Span) -> None:
        with push_span.span('Redundancy'):
            start = time.perf_counter()

            f_inf = list(self.frame_lemmas(None))
            for i in f_inf:
                if i in self._safeties: continue # don't mark safety properties as redundant
                result = await self._redundancy_checker.check_implication([self._lemmas[j] for j in self.frame_lemmas(None) if i != j], self._lemmas[i], parallelism=self._pushing_parallelism, timeout=10)
                if result.result == SatResult.unsat:
                    print(f"Redundant lemma: {self._lemmas[i]}")
                    self._redundant_lemmas.add(i)

            print(f"Checked redundancy in {time.perf_counter() - start:0.3f} sec")

    async def push(self) -> None:
        async with self._push_lock:
            with self._span.span('Push') as push_span:
                start = time.perf_counter()
                frame_num = 0

                while True:
                    for index in range(len(self._lemmas)):
                        if self._frame_numbers[index] == frame_num:
                            await self._push_lemma(index, push_span)

                    if frame_num > 0 and not any(fn == frame_num for fn in self._frame_numbers):
                        # frame is empty, sweep all greater finite frames to f_inf
                        swept_to_f_inf = 0
                        for index in range(len(self._lemmas)):
                            fn = self._frame_numbers[index]
                            if fn is not None and frame_num <= fn:
                                print(f"Pushed {'lemma' if index not in self._safeties else 'safety'} to frame inf: {self._lemmas[index]}")
                                self._frame_numbers[index] = None
                                swept_to_f_inf += 1
                        if swept_to_f_inf > 0:
                            await self._check_f_inf_redundancy(push_span)
                        break
                    frame_num += 1
                print(f"Pushing completed in {time.perf_counter() - start:0.3f} sec")

    async def wait_for_frame_update(self) -> None:
        await self._event_frame_update.wait()

    async def wait_for_completion(self) -> bool:
        while True:
            await self._event_frame_update.wait()
            async with self._push_lock:
                if all(self._frame_numbers[i] is None for i in self._safeties):
                    return True
                # TODO: check for unsafe-ness
                # if any():
                #     pass

    async def get_blocker(self, lemm: int) -> Optional[Blocker]:
        async with self._push_lock:
            if self._frame_numbers[lemm] is None or self._is_bad_lemma(lemm):
                return None
            return self._ultimate_pushing_blocker[lemm]

    async def speculative_push(self, l: Expr, frame: int, b: Blocker) -> Optional[Blocker]:
        assert b.frame <= frame
        if b.type_is_predecessor:
            assert b.successor != -1

            if not all(self.eval(f_i, b.successor) for f_i in self.frame_lemmas(b.frame + 1)):
                print("Didn't speculate because post-state is not in next frame")
                return None

            # We need to check for a predecessor
            s = self._states[b.successor]
            formula_to_block = syntax.Not(s.as_onestate_formula() if utils.args.logic != "universal" else Diagram(s).to_ast())
            # We do this in a loop to ensure that if someone concurrently modifies the frames, we still compute a correct
            # predecessor. This is only currently used to ensure that speculative_push() doesn't need to synchronize with push()
            while True:
                fp = set(self.frame_lemmas(frame))
                # edge = check_transition(self._solver, [self._predicates[i] for i in self.frame_predicates(frame-1)], formula_to_block, minimize=False)
                #edge = await robust_check_transition([self._predicates[i] for i in fp], formula_to_block, minimize='no-minimize-block' not in utils.args.expt_flags, parallelism=2, log=self._logs._smt_log)
                edge = await self._predecessor_robust_checker.check_transition([*(self._lemmas[i] for i in fp), l], formula_to_block, parallelism=self._pushing_parallelism)
                if fp != set(self.frame_lemmas(frame)):
                    continue
                break
            if isinstance(edge.trace, Trace):
                pred = await self.add_state(edge.trace.as_state(0))
                await self.add_transition(pred, b.successor)
                blocker_data = Blocker(state=pred, frame=b.frame, successor=b.successor, type_is_predecessor=True)
                return blocker_data
            elif edge.result == SatResult.unsat:
                print("Didn't speculate because post-state has no predecessors")
                return None
            else:
                assert False


        assert b.lemma != -1
        lemm = b.lemma
        i = frame
        p = self._lemmas[lemm]

        if self._frame_numbers[lemm] != i:
            print("Didn't speculate because lemma has been pushed")
            return None
        if self._is_bad_lemma(lemm) or lemm in self._pushability_unknown_lemmas:
            print("Didn't speculate because lemma is bad or has unknown pushability")
            return None
        while True:
            fp = set(self.frame_lemmas(i))
            if lemm not in self._push_robust_checkers:
                self._push_robust_checkers[lemm] = AdvancedChecker(syntax.the_program, self._logs._smt_log) if 'no-advanced-checker' not in utils.args.expt_flags else ClassicChecker(self._logs._smt_log)

            time_limit = 0.0 if lemm in self._safeties else self._pushing_timeout
            cex = await self._push_robust_checkers[lemm].check_transition([*(self._lemmas[j] for j in fp), l], p, parallelism=self._pushing_parallelism, timeout=time_limit)
            if fp != set(self.frame_lemmas(i)):
                # Set of predicates changed across the await call. To avoid breaking the meta-invariant, loop around for another iteration
                continue
            if cex.result == SatResult.unsat:
                print(f"speculatively pushed {p} to frame {i+1}")
                return None
            elif cex.result == SatResult.sat and isinstance(cex.trace, Trace):
                trace = cex.trace
                # Add the blocker and the sucessor state. We need the successor state because
                # if we show the blocker is reachable, it is actually the successor that invalidates
                # the lemma and is required to mark it as bad
                blocker = await self.add_state(trace.as_state(0))
                blocker_successor = await self.add_state(trace.as_state(1))
                await self.add_transition(blocker, blocker_successor)

                # Add the state as a "former" blocker even though it hasn't been used as such. This means that
                # if the speculative blocking fails, this blocker will be picked up as the blocking state next
                self._former_pushing_blockers[lemm][blocker] = None
                blocker_data = Blocker(state=blocker, frame=i, lemma=lemm, type_is_predecessor=False)
                actual_blocker = await self._blockable_state(blocker_data)
                if actual_blocker is None:
                    print("Didn't speculate because blocker is reachable")
                    return None
                if actual_blocker.frame != i:
                    print("Didn't speculate because actual blocker in another frame")
                    return None
                return blocker_data
            elif lemm not in self._safeties and cex.result == SatResult.unknown:
                print(f"Pushability unknown: {p}")
                print("Didn't speculate because pushability is unknown")
                self._pushability_unknown_lemmas.add(lemm)
                return None
            else:
                print(f"cex {cex.result}")
                assert False

class ParallelFolIc3:
    FrameNum = Optional[int]
    def __init__(self, span: Tracer.Span) -> None:
        # Logging, etc
        self._start_time: float = 0
        self._root_span = span
        self._logs = Logging(utils.args.log_dir)
        self._next_ig_query_index = 0

        self._sig = prog_to_sig(syntax.the_program, two_state=False)

        cpus = os.cpu_count()
        thread_budget = utils.args.cpus if utils.args.cpus is not None else (cpus if cpus is not None else 1)
        self._threads_per_ig_heuristic = 0 if 'no-heuristic-pushing' in utils.args.expt_flags else thread_budget // 2
        self._threads_per_ig_learning = thread_budget - self._threads_per_ig_heuristic
        self._threads_per_push = self._threads_per_ig_learning

        if 'sequential' in utils.args.expt_flags:
            self._threads_per_ig_learning = 1
            self._threads_per_ig_heuristic = 1
        
        self._current_push_heuristic_tasks: Set[Tuple[int,int]] = set() # Which (frame, state) pairs are being worked on by the push heuristic?
        self._frames = IC3Frames(self._logs, self._root_span, self._threads_per_ig_learning)


        if 'sequential' in utils.args.expt_flags:
            self._frames._pushing_timeout = 6 * self._frames._pushing_timeout

    def print_frames(self) -> None:
        self._frames.print_lemmas()
        elapsed = time.perf_counter() - self._start_time
        print(f"time: {elapsed:0.3f} sec")
        self._frames.log_frames(elapsed = elapsed)

    async def init(self) -> None:
        prog = syntax.the_program
        for init_decl in prog.inits():
            i = await self._frames.add_lemma(init_decl.expr)
            self._frames._initial_conditions.add(i)
        for safety_decl in prog.safeties():
            i = await self._frames.add_lemma(safety_decl.expr)
            self._frames._safeties.add(i)
            self._frames._frame_numbers[i] = 1
        if 'free-lemma' in utils.args.expt_flags:
            for inv_decl in prog.invs():
                if inv_decl.name == 'free_lemma':
                    i = await self._frames.add_lemma(inv_decl.expr)
                    self._frames._frame_numbers[i] = 1

    async def parallel_inductive_generalize(self, b: Blocker, threads: int = 1, rationale: str = '', timeout: Optional[float] = None, prior_solver: Optional[IGSolver] = None) -> IGSolver:
        ig_frame = set(self._frames.frame_lemmas(b.frame-1))
        ig_solver = IGSolver(self._frames._states[b.state],
                                  [self._frames._states[x] for x in self._frames._useful_reachable | self._frames._initial_states],
                                  [self._frames._lemmas[x] for x in ig_frame],
                                  self._logs, syntax.the_program, rationale, self._next_ig_query_index, prior_solver)
        self._next_ig_query_index += 1
        self._logs._ig_queries_pickler.dump({"log_prefix": ig_solver._log_prefix, 
                                             "rationale": ig_solver._rationale, 
                                             "necessary_constraints": list(ig_solver._necessary_constraints),
                                             "reachable": list(ig_solver._reachable_constraints),
                                             "states": ig_solver._states,
                                             "frame": ig_solver._frame})
        self._logs._ig_queries_log.flush()

        negative_states = set([b.state])
        sol: asyncio.Future[Optional[Expr]] = asyncio.Future()

        async def frame_updater()-> None:
            while True:
                current_frame = set(self._frames.frame_lemmas(b.frame - 1))
                if ig_frame != current_frame:
                    for f in current_frame - ig_frame:
                        ig_solver.add_to_frame(self._frames._lemmas[f])
                await self._frames.wait_for_frame_update()

        async def concurrent_block()-> None:
            while True:
                if all(any(not self._frames.eval(l, n) for l in self._frames.frame_lemmas(b.frame)) for n in negative_states):
                    print(f"States blocked in frame {b.frame} by concurrent task")
                    if not sol.done():
                        sol.set_result(None)
                    else:
                        break
                await self._frames.wait_for_frame_update()

        async def solver(IG_span: Tracer.Span) -> None:
            with IG_span.span('Solve') as solve_span:
                main_solve_start = time.perf_counter()
                p = await ig_solver.solve(threads, timeout = timeout, span = solve_span)
                main_solve_time = time.perf_counter() - main_solve_start

            if p is None:
                if not sol.done():
                    sol.set_result(None)
                return

            if 'no-multi-generalize' not in utils.args.expt_flags:
                time_to_generalize = 1.0 * main_solve_time + 0.1
                generalizations_found = 0
                while True:
                    with IG_span.span('Gen') as solve_span:
                        gen_solve_start = time.perf_counter()
                        if p is None:
                            break
                        new_blocker = await self._frames.speculative_push(p, b.frame, b)
                        if new_blocker is None:
                            break

                        # The new state should satisfy the current candidate p
                        assert eval_predicate(self._frames._states[new_blocker.state], p)

                        negative_states.add(new_blocker.state)
                        ig_solver.add_negative_state(self._frames._states[new_blocker.state])

                        new_p = await ig_solver.solve(threads, timeout = time_to_generalize, span = solve_span)

                        if new_p is None:
                            print("Failed to find generalized lemma in time")
                            break
                        p = new_p
                        print(f"Generalized to {p}")
                        generalizations_found += 1
                        gen_solve_end = time.perf_counter()
                        time_to_generalize -= gen_solve_end-gen_solve_start
                        if time_to_generalize < 0.005: break
                print(f"Generalized a total of {generalizations_found} times")

            if not sol.done():
                sol.set_result(p)


        with self._root_span.span('IG', ig_solver._identity) as IG_span:
            IG_span.data(rationale=rationale)
            async with ScopedTasks() as tasks:
                tasks.add(frame_updater())
                tasks.add(concurrent_block())
                tasks.add(solver(IG_span))
                final_p = await sol
            IG_span.data(result=None if final_p is None else str(final_p))
        if final_p is None:
            print(f"IG query cancelled ({b.state} in frame {b.frame} for {rationale})")
            return ig_solver

        print(f"Learned new lemma {final_p} blocking {b.state} in frame {b.frame} for {rationale}")
        lemma = await self._frames.add_lemma(final_p, b.frame)
        IG_span.data(lemma=lemma)
        await self._frames.push()
        self.print_frames()
        return ig_solver

    def heuristic_priority(self, pred: int, frame_N: Optional[int] ) -> Any:
        def mat_size(e: Expr) -> int:
            if isinstance(e, QuantifierExpr): return mat_size(e.body)
            elif isinstance(e, UnaryExpr): return mat_size(e.arg)
            elif isinstance(e, NaryExpr): return sum(map(mat_size, e.args))
            elif isinstance(e, BinaryExpr): return mat_size(e.arg1) + mat_size(e.arg2)
            else: return 1
        fn = self._frames._frame_numbers[pred]
        return (-fn if fn is not None else 0, mat_size(self._frames._lemmas[pred]) + random.random() * 0.5)

    async def heuristic_pushing_to_the_top_worker(self) -> None:
        # print("Starting heuristics")
        timeouts = [128.0, 256.0, 512.0, 1024.0]
        # timeouts: List[float] = []
        timeout_index = 0
        current_timeout: Dict[Tuple[int, int], int] = {}
        while True:
            frame_N = min((self._frames._frame_numbers[s] for s in self._frames._safeties), key = IC3Frames.frame_key)
            priorities = sorted(range(len(self._frames._lemmas)), key=lambda lemm: self.heuristic_priority(lemm, frame_N))
            # print("Heuristic priorities:")
            # for lemm in priorities:
            #     print(f"     -> {self._frames._lemmas[lemm]}")
            
            for lemm in priorities:
                # Don't push anything past the earliest safety
                if IC3Frames.frame_leq(frame_N, self._frames._frame_numbers[lemm]):
                    continue
                
                blocker = await self._frames.get_blocker(lemm)
                if blocker is None:
                    continue

                fn, st = blocker.frame, blocker.state
                assert fn is not None
                if (fn, st) in self._current_push_heuristic_tasks:
                    continue
                index = current_timeout.get((fn, st), 0)
                if index > timeout_index:
                    continue
                try:
                    self._current_push_heuristic_tasks.add((fn, st))
                    timeout = timeouts[timeout_index] if timeout_index < len(timeouts) else None
                    print(f"Heuristically blocking state {st} in frame {fn} to push {self._frames._lemmas[lemm]} (timeout {timeout})")
                    await self.parallel_inductive_generalize(blocker, self._threads_per_ig_heuristic, 'heuristic-push', timeout=timeout)

                    current_timeout[(fn, st)] = timeout_index + 1
                    timeout_index = 0
                finally:
                    self._current_push_heuristic_tasks.remove((fn, st))
                break
            else:
                # print("Couldn't find job to do in heuristic-push")
                if timeout_index < len(timeouts):
                    # print("Increasing timeout limit in heuristic task")
                    timeout_index += 1
                    continue
                await self._frames.wait_for_frame_update()
                timeout_index = 0

    # This is the main loop responsible for learning classic IC3 lemmas by blocking bad states or backwardly reachable from bad
    async def learn(self) -> None:
        prior_solver: Optional[IGSolver] = None
        while True:
            for safety in sorted(self._frames._safeties, key = lambda x: IC3Frames.frame_key(self._frames._frame_numbers[x])):
                blockable = await self._frames.get_blocker(safety)
                if blockable is None:
                    break # try again with new safety property (as by the time we call get_blocker() the safety property may have moved)
                    # we rely on cancellation (from await self._frames.wait_for_completion()) to stop this loop
                new_solver = await self.parallel_inductive_generalize(blockable, self._threads_per_ig_learning, rationale="learning", timeout = None, prior_solver = prior_solver)
                prior_solver = new_solver
                break
            else:
                return

    async def flush_trace(self) -> None:
        while True:
            self._root_span.flush()
            await asyncio.sleep(3)

    async def run(self) -> None:
        self._start_time = time.perf_counter()
        await self.init()
        await self._frames.push()
        self.print_frames()
        async with ScopedTasks() as tasks:
            tasks.add(self.flush_trace())
            if 'no-heuristic-pushing' not in utils.args.expt_flags:
                tasks.add(self.heuristic_pushing_to_the_top_worker())
            # tasks.add(self.inexpensive_reachability())
            tasks.add(self.learn())
            await self._frames.wait_for_completion()

        print(f"Elapsed: {time.perf_counter() - self._start_time:0.3f} sec")
        if all(self._frames._frame_numbers[i] is None for i in self._frames._safeties):
            print("Program is SAFE.")
            for frame, (index, p) in zip(self._frames._frame_numbers, enumerate(self._frames._lemmas)):
                if frame is None and index not in self._frames._safeties and index not in self._frames._redundant_lemmas:
                    print(f"  invariant [inferred] {p}")
        else:
            print("Program is UNSAFE/UNKNOWN.")

def p_fol_ic3(_: Solver) -> None:
    # Redirect stdout if we have a log directory
    if utils.args.log_dir:
        os.makedirs(utils.args.log_dir, exist_ok=True)
        for dir in ['smt-queries', 'eval']:
            os.makedirs(os.path.join(utils.args.log_dir, dir), exist_ok=True)
        sys.stdout = io.TextIOWrapper(open(os.path.join(utils.args.log_dir, "main.log"), "wb"), line_buffering=True, encoding='utf8')

    if 'no-epr' in utils.args.expt_flags and utils.args.logic == 'epr':
        utils.args.logic = 'fol'

    # Print initial header with command line
    print(f"ParallelFolIC3 log for {os.path.basename(utils.args.filename)}")
    print(f"Command line: {' '.join(sys.argv)}")
    print(f"Expt-flags: {', '.join(utils.args.expt_flags)}")
    print(f"Logic: {utils.args.logic}")

    get_forkserver() # Cause the forkserver to start here
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
        trace_file = os.path.join(utils.args.log_dir, "trace.pickle") if utils.args.log_dir else '/dev/null'
        with trace(open(trace_file, 'wb')) as tracer:
            p = ParallelFolIc3(tracer)
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

    if 'summarize' in utils.args.expt_flags:
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
        sizes = []
        for x in prog.invs():
            if x.is_safety: continue
            conjuncts += 1
            quants = max(quants, count_quantifiers(x.expr))
            sizes.append(count_quantifiers(x.expr))
        sig = prog_to_sig(syntax.the_program)

        edges: Set[Tuple[str, str]] = set()
        for func in syntax.the_program.functions():
            for s1 in func.arity:
                edges.add((str(s1), str(func.sort)))
        sol = Solver()
        t = sol.get_translator(2)
        with sol.new_frame():
            for inv in prog.invs():
                sol.add(t.translate_expr(inv.expr))
                sol.add(t.translate_expr(Not(New(inv.expr))))
            for trans in prog.transitions():
                sol.add(t.translate_expr(trans.as_twostate_formula(prog.scope)))
            for a in sol.z3solver.assertions():
                add_epr_edges(edges, a)
        #print('epr_edges =',repr(','.join(f'{a}->{b}' for a,b in edges)))
        g = networkx.DiGraph()
        g.add_edges_from(edges)
        epr = 'Y' if networkx.is_directed_acyclic_graph(g) else ''

        print(f"{base_name}&{epr}&{conjuncts}&{quants}&{len(sig.sorts)}&{len(sig.relations) + len(sig.constants) + len(sig.functions)}")
        # print(sizes)
    if 'epr' in utils.args.expt_flags:
        # Check EPR-ness
        edges2: Set[Tuple[str, str]] = set()
        for func in syntax.the_program.functions():
            for s1 in func.arity:
                edges2.add((str(s1), str(func.sort)))
        sol = Solver()
        t = sol.get_translator(2)

        for trans in prog.transitions():
            with sol.new_frame():
                sol.add(t.translate_expr(trans.as_twostate_formula(prog.scope)))
                for a in sol.z3solver.assertions():
                    old_edges = set(edges2)
                    add_epr_edges(edges2, a)
                    if len(edges2-old_edges) > 0:
                        if 'debug' in utils.args.expt_flags:
                            print(f"Assertion {a} added {edges2-old_edges}")
                            print("trans", trans.name)

        for inv in prog.invs():
            with sol.new_frame():
                sol.add(t.translate_expr(inv.expr))
                sol.add(t.translate_expr(Not(New(inv.expr))))
                for a in sol.z3solver.assertions():
                    old_edges = set(edges2)
                    add_epr_edges(edges2, a)
                    if len(edges2-old_edges) > 0:
                        if 'debug' in utils.args.expt_flags:
                            print(f"Assertion added {edges2-old_edges}")
                            print("inv", inv)
        def exists_in(e: Expr, polarity: bool = True) -> bool:
            if isinstance(e, QuantifierExpr):
                is_exists = (e.quant == 'EXISTS') == polarity
                return is_exists or exists_in(e.body, polarity)
            elif isinstance(e, UnaryExpr):
                if e.op == 'NOT':
                    return exists_in(e.arg, not polarity)
                else:
                    return exists_in(e.arg)
            elif isinstance(e, BinaryExpr):
                if e.op == 'IMPLIES':
                    return exists_in(e.arg1, not polarity) or exists_in(e.arg2, polarity)
                elif e.op == 'IFF':
                    return exists_in(e.arg1, polarity) or exists_in(e.arg2, polarity) or exists_in(e.arg1, not polarity) or exists_in(e.arg2, not polarity)
                return exists_in(e.arg1, polarity) or exists_in(e.arg2, polarity)
            elif isinstance(e, NaryExpr):
                return any(exists_in(c, polarity) for c in e.args)
            elif isinstance(e, IfThenElse):
                return exists_in(e.branch, polarity) or exists_in(e.branch, not polarity) or exists_in(e.then, polarity) or exists_in(e.els, polarity)
            elif isinstance(e, Let):
                return exists_in(e.body, polarity) or exists_in(e.val, polarity)
            else:
                return False

        has_exists = False
        for inv in prog.invs():
            has_exists = exists_in(inv.expr) or has_exists

        if 'debug' in utils.args.expt_flags:
            print(f"Final edges: {edges2}")
        g = networkx.DiGraph()
        g.add_edges_from(edges2)

        #print(f"graph is acyclic: {networkx.is_directed_acyclic_graph(g)}")
        if networkx.is_directed_acyclic_graph(g):
            remaining = set(s.name for s in prog.sorts())
            redges = list(edges2)
            result: List[str] = []
            while len(remaining) > 0:
                for r in sorted(remaining):
                    if all(e[1] != r for e in redges):
                        result.append(r)
                        redges = [e for e in redges if e[0] != r]
                        remaining.remove(r)
                        break
                else:
                    assert False, "not acyclic"
            print()
            for r in result:
                print(f"sort {r}")
            print()
        if has_exists:
            if networkx.is_directed_acyclic_graph(g):
                print('--logic=epr', '--epr-edges=' + repr(','.join(f'{a}->{b}' for a,b in edges2)), utils.args.filename)
            else:
                print('--logic=fol', utils.args.filename)
        else:
            print('--logic=universal', utils.args.filename)

    if 'print-old-transitions' in utils.args.expt_flags:
        def has_new(e: Expr) -> bool:
            if isinstance(e, UnaryExpr) and e.op == 'NEW':
                return True
            if isinstance(e, (syntax.Bool, syntax.Int)):
                return False
            elif isinstance(e, UnaryExpr):
                return has_new(e.arg)
            elif isinstance(e, BinaryExpr):
                return has_new(e.arg1) or has_new(e.arg2)
            elif isinstance(e, NaryExpr):
                return any(has_new(arg) for arg in e.args)
            elif isinstance(e, AppExpr):
                return any(has_new(arg) for arg in e.args)
            elif isinstance(e, QuantifierExpr):
                return has_new(e.body)
            elif isinstance(e, syntax.Id):
                return False
            elif isinstance(e, IfThenElse):
                return has_new(e.branch) or has_new(e.then) or has_new(e.els)
            elif isinstance(e, Let):
                return has_new(e.val) or has_new(e.body)
            else:
                assert False, (type(e), e)
        def to_old(e: Expr) -> Expr:
            if not has_new(e):
                return AppExpr('old', (e,), span=e.span)
            if isinstance(e, UnaryExpr) and e.op == 'NEW':
                return e.arg

            if isinstance(e, (syntax.Bool, syntax.Int)):
                return e
            elif isinstance(e, UnaryExpr):
                return UnaryExpr(e.op, to_old(e.arg), span=e.span)
            elif isinstance(e, BinaryExpr):
                return BinaryExpr(e.op, to_old(e.arg1), to_old(e.arg2), span=e.span)
            elif isinstance(e, NaryExpr):
                return NaryExpr(e.op, tuple(to_old(arg) for arg in e.args), span=e.span)
            elif isinstance(e, AppExpr):
                new_args = tuple(to_old(arg) for arg in e.args)
                return AppExpr(e.callee, new_args, span=e.span)
            elif isinstance(e, QuantifierExpr):
                return QuantifierExpr(e.quant, e.binder.vs, to_old(e.body), span=e.span)
            elif isinstance(e, syntax.Id):
                assert False, "should have already concluded not has-new"
            elif isinstance(e, IfThenElse):
                return IfThenElse(to_old(e.branch), to_old(e.then), to_old(e.els), span=e.span)
            elif isinstance(e, Let):
                assert len(e.binder.vs) == 1
                new_val = to_old(e.val)
                new_body = to_old(e.body)
                return Let(e.binder.vs[0], new_val, new_body, span=e.span)
            else:
                assert False, (type(e), e)

        with open(utils.args.output, 'w') as f:
            print(f"# Mypyvy old syntax auto-generated from {os.path.basename(utils.args.filename)}", file=f)
            prev: Optional[syntax.Decl] = None
            for decl in syntax.the_program.decls:
                if prev is not None and type(decl) != type(prev):
                    print("", file=f)
                if isinstance(decl, DefinitionDecl) and decl.num_states == 2:
                    decl.expr = to_old(decl.expr)
                if not isinstance(decl, TraceDecl):
                    print(decl, file=f)
                prev = decl

def fol_learn(solver: Solver) -> None:
    get_forkserver()
    async def main() -> None:
        sig = prog_to_sig(syntax.the_program)
        golden = [inv for inv in syntax.the_program.invs() if not inv.is_safety][utils.args.index].expr
        print("Target:", golden)

        checker = AdvancedChecker(syntax.the_program)
        

        pc = PrefixConstraints()
        if utils.args.logic == 'epr':
            pc.logic = Logic.EPR
        else:
            pc.logic = Logic.FOL
        constraints: List[Union[Pos, Neg]] = []
        states: List[State] = []
        prefixes = PrefixQueue(sig, pc.logic, True)

        while True:
            (prefix, prefix_index) = prefixes.get_prefix()
            print("Trying ", prefix.linearize())
            sep = FixedImplicationSeparatorPyCryptoSat(sig, prefix.linearize(), pc = pc, k_cubes=3)
            to_sep = {}
            current_constraints = set()
            def add_constraint(c: Union[Neg, Pos]) -> None:
                if c in current_constraints: return
                if c.i not in to_sep:
                    to_sep[c.i] = sep.add_model(state_to_model(states[c.i]))
                sep.add_constraint(c.map(to_sep))
                current_constraints.add(c)
            while True:
                p = sep.separate(minimize=True)
                if p is None:
                    prefixes.complete_prefix(prefix)
                    break
                with syntax.the_program.scope.n_states(1):
                    pp = formula_to_predicate(p, syntax.the_program.scope)
                print("Separator:", pp)
                for c in constraints:
                    if not satisifies_constraint(c, pp, states):
                        add_constraint(c)
                        break
                else:
                    query_r = await checker.check_implication([pp], golden, parallelism=2)
                    if query_r.trace is not None:
                        i = len(states)
                        states.append(query_r.trace.as_state(0))
                        constraints.append(Neg(i))
                        add_constraint(Neg(i))
                        print("Added negative constraint")
                        continue
                    query_s = await checker.check_implication([golden], pp, parallelism=2)
                    if query_s.trace is not None:
                        i = len(states)
                        states.append(query_s.trace.as_state(0))
                        constraints.append(Pos(i))
                        add_constraint(Pos(i))
                        print("Added positive constraint")
                        continue
                    if query_r.result == SatResult.unsat and query_s.result == SatResult.unsat:
                        print("Matches")
                        return
                    else:
                        print("Error, unknown")
                        return
    asyncio.run(main())
    pass

def add_epr_edges(edges: Set[Tuple[str, str]], expr: z3.ExprRef, polarity: bool = True, univ_sorts: Set[str] = set()) -> None:
    if z3.is_quantifier(expr):
        assert isinstance(expr, z3.QuantifierRef)
        is_universal = polarity == expr.is_forall()
        sorts = [expr.var_sort(i).name() for i in range(expr.num_vars())]
        if is_universal:
            univ_sorts = univ_sorts | set(sorts)
        else:
            for s in univ_sorts:
                for t in sorts:
                    edges.add((s, t))
        add_epr_edges(edges, expr.body(), polarity, univ_sorts)
    elif z3.is_app(expr):
        children = expr.children()
        if z3.is_and(expr) or z3.is_or(expr):
            for c in children:
                add_epr_edges(edges, c, polarity, univ_sorts)
        elif z3.is_not(expr):
            for c in children:
                add_epr_edges(edges, c, not polarity, univ_sorts)
        elif z3.is_implies(expr):
            assert len(children) == 2
            add_epr_edges(edges, children[0], not polarity, univ_sorts)
            add_epr_edges(edges, children[1], polarity, univ_sorts)
        elif z3.is_app_of(expr, z3.Z3_OP_ITE):
            add_epr_edges(edges, children[0], not polarity, univ_sorts)
            add_epr_edges(edges, children[0], polarity, univ_sorts)
            add_epr_edges(edges, children[1], polarity, univ_sorts)
            add_epr_edges(edges, children[2], polarity, univ_sorts)
        else:
            pass # print(f"{expr}")

    else:
        assert False

def fol_benchmark_solver(_: Solver) -> None:
    get_forkserver()
    # Verify, but with CVC5Solver
    # from solver_cvc5 import CVC5Solver, SatResult
    # solver = CVC5Solver(syntax.the_program)
    # with solver.new_scope(1):
    #     for tr in syntax.the_program.transitions():
    #         with solver.new_scope(2):
    #             print(f"Transition {tr.name}")
    #             solver.add_expr(tr.as_twostate_formula(syntax.the_program.scope))
    #             for inv in syntax.the_program.invs():
    #                 solver.add_expr(inv.expr)

    #             for inv_to_check in syntax.the_program.invs():
    #                 with solver.new_scope(2):
    #                     print(f"Checking {inv_to_check}", end = '... ', flush=True)
    #                     solver.add_expr(New(Not(inv_to_check.expr)))
    #                     res = solver.check()
    #                     if res is not SatResult.unsat:
    #                         print(res)
    #                         print("System unsafe.")
    #                         # print(solver.get_trace())
    #                         return
    #                     else:
    #                         print("unsat.")
    # print("Check complete, system is safe.")
    # return

    if utils.args.output:
        sys.stdout = open(utils.args.output, "w")
    print(f"Benchmarking {utils.args.query} ({utils.args.filename})")
    data = pickle.load(open(utils.args.query, 'rb'))
    if len(data) == 2:
        (old_hyps, new_conc) = cast(Tuple[List[Expr], Expr], data)
        states = 2
    else:
        assert False

    if True:
        for e in old_hyps:
            print("  ", e)
        print("  ", new_conc)
        print("testing checker")
        start_time = time.perf_counter()
        checker = AdvancedChecker(syntax.the_program) if 'no-advanced-checker' not in utils.args.expt_flags else ClassicChecker()
        r_r = asyncio.run(checker.check_transition(old_hyps, new_conc, 1, 1000000.0))
        end_time = time.perf_counter()
        print (r_r.result)
        print (f"=== Solution obtained in {end_time-start_time:0.3f}")

        # print(checker._last_successful)
        # print(checker._transitions)

        start_time = time.perf_counter()
        r_r = asyncio.run(checker.check_transition(old_hyps, new_conc, 1, 1000000.0))
        end_time = time.perf_counter()
        print (r_r.result)
        print (f"=== Solution obtained in {end_time-start_time:0.3f}")


def fol_benchmark_ig(_: Solver) -> None:
    tp = Tuple[str, Neg, List[Constraint], Dict[int, State], List[Expr], List[InvariantDecl]]
    (rationale, block, pos, states, prior_frame, golden) = cast(tp, pickle.load(open(utils.args.query, 'rb')))
    print(f"IG query for {rationale}")
    async def run_query() -> None:
        logs = Logging('')
        logs._smt_log = open('/dev/null', 'w')
        logs._sep_log = open('/dev/null', 'w')
        # if 'ig2' in utils.args.expt_flags:
        ig2 = IGSolver(states[block.i],
                        [states[x.i] for x in pos if isinstance(x, Pos)],
                        prior_frame,
                        logs, syntax.the_program, rationale, 0)
        await ig2.solve(10)

        # else:
        #     ig = IGSolver(states[block.i],
        #                   [states[x.i] for x in pos if isinstance(x, Pos)],
        #                   prior_frame,
        #                   logs, syntax.the_program, rationale, 0)
        #     await ig.solve(10)


    asyncio.run(run_query())


def fol_benchmark_eval(_: Solver) -> None:
    total = 0.0
    for input_fname in os.listdir(utils.args.query):
        with open(os.path.join(utils.args.query, input_fname), 'rb') as f:
            try:
                data: Tuple[Dict[int, State], Expr] = pickle.load(f)
            except EOFError:
                continue
            (states, p) = data

            start = time.perf_counter()
            for key, st in states.items():
                value = st.eval(p)
                #print(st.eval(p), ','.join(f'{len(l)}' for l in st.univs.values()))
            end = time.perf_counter()
            print(f"elapsed: {1000.0*(end-start)/len(states):0.3f} ms/eval {p}")
            total += end-start
    print(f"overall: {total:0.3f}")


def fol_debug_ig(_: Solver) -> None:
    get_forkserver()

    async def find_minimal_addition(checker: RobustChecker, frame: List[Expr], inv: Expr) -> None:
        candidate_core: List[Expr] = []
        candidates = [human_inv.expr for human_inv in syntax.the_program.invs() if human_inv]
        n = max(1, len(candidates) // 2)
        model: Optional[Trace] = None
        while len(candidates) > 0:
            
            # try without c
            res = await checker.check_transition(frame + candidate_core + candidates[n:] + [inv], inv, parallelism=2, timeout=500)
            if res.result == SatResult.unsat:
                model = None
                candidates = candidates[n:] # didn't need anything in candidates[:n]
                n = max(1, len(candidates) // 2)
                
            elif res.result == SatResult.sat or res.result == SatResult.unknown:
                if n == 1:
                    model = res.trace
                    candidate_core.append(candidates[0]) # we needed c after all
                    candidates = candidates[n:]
                else:
                    n = max(1, n // 2)
                    random.shuffle(candidates)
        
        print("Core is:")
        for i in candidate_core:
            print(" ", i)

    async def main() -> None:
        # if utils.args.output:
        #     sys.stdout = open(utils.args.output, "w")
        print(f"Benchmarking {utils.args.query} ({utils.args.filename})")
        data_stream = pickle.Unpickler(open(os.path.join(utils.args.log_dir, "ig-queries.pickle"), 'rb'))
        data: Optional[dict] = None
        while True:
            try:
                query_data = data_stream.load()
                if query_data['rationale'] == 'learning':
                    data = query_data
            except EOFError:
                break
        if data is None:
            print("No query")
            return

        log_prefix: str = data['log_prefix']
        rationale: str = data['rationale']
        necessary_constraints: List[Constraint] = data['necessary_constraints']
        states: List[State] = data['states']
        frame: List[Expr] = data["frame"]


        print(f"Results for IG query {log_prefix} {rationale}")

        state_to_block: State = states[cast(Neg, necessary_constraints[0]).i]
        for human_inv in syntax.the_program.invs():
            i = human_inv.expr
            if not state_to_block.eval(i):
                print(f"{i} blocks the proof obligation")
                checker = AdvancedChecker(syntax.the_program, log=open("/dev/null", 'w')) if 'no-advanced-checker' not in utils.args.expt_flags else ClassicChecker()
                res = await checker.check_transition(frame + [i], i, parallelism=10, timeout=500)
                if res.result == SatResult.unsat:
                    print("relatively inductive (solution)")
                elif res.result == SatResult.unknown:
                    print("relative inductiveness unknown")
                else:
                    print("not relatively inductive to frame (not solution)")
                    await find_minimal_addition(checker, frame, i)
                
    asyncio.run(main())

def fol_debug_frames(_: Solver) -> None:
    get_forkserver()
    async def main() -> None:
        lemmas = {}
        with open(os.path.join(utils.args.log_dir, "lemmas.pickle"), 'rb') as lemmas_pickle:
            try:
                while True:
                    lemma = pickle.load(lemmas_pickle)
                    lemmas.update(lemma)
            except EOFError:
                pass
        frames = []
        with open(os.path.join(utils.args.log_dir, "frames.pickle"), 'rb') as frames_pickle:
            try:
                while True:
                    f = pickle.load(frames_pickle)
                    frames.append(f)
            except EOFError:
                pass
        # with open(os.path.join(utils.args.log_dir, "trace.pickle"), 'rb') as f:
        #     trace = load_trace(f)
        #     # print(trace)
        #     # data = []
        #     for ig_query in trace.descendants('IG'):
        #         # print(ig_query, file = open('ig-query.txt', 'w'))
        #         # return
        #         if ig_query.data['rationale'] != 'learning':
        #             continue
        #         solve_phase = next(ig_query.descendants('Solve'))
        #         for prefix_query in solve_phase.descendants('Pre'):
        #             if 'sep' in prefix_query.data:
        #                 t = 0.0
        #                 for x in prefix_query.descendants('Sep'):
        #                     t += x.duration
        #                 print(f"{solve_phase.duration:0.3f} {prefix_query.duration:0.3f} {len(prefix_query.data['prefix'].linearize())} {t/prefix_query.duration:0.3f}")
        #                 for x in prefix_query.descendants('SMT-tr'):
        #                     print (f"{x.duration:0.3f}")

        #     with open("smt-tr-times.csv", 'w') as f:        
        #         for ig_query in trace.descendants('IG'):
        #             for x in ig_query.descendants('SMT-tr'):
        #                 print(f"{x.duration:0.3f} {x.data['result'] if 'result' in x.data else 'unknown'}", file=f)

        #     print ("\n\n\n")
        #     with open("prefix-times-scatter.csv", 'w') as f:
        #         for index, ig_query in enumerate(trace.descendants('IG')):
        #             if ig_query.data['rationale'] != 'learning':
        #                 continue
        #             solve_phase = next(ig_query.descendants('Solve'))
        #             for prefix_query in solve_phase.descendants('Pre'):
        #                 code = 1 if 'unsep' in prefix_query.data else 2 if 'sep' in prefix_query.data else 3
        #                 print(f"{index}, {prefix_query.duration:0.3f}, {code}", file=f)

        #         # times: DefaultDict[int, float] = defaultdict(lambda: 0.0)
        #         # for prefix_query in ig_query.descendants('Pre'):
        #         #     times[prefix_query.data['category']] += prefix_query.duration
        #         #     # print(f"{prefix_query.data['category']} {prefix_query.duration:0.3f}")
        #         # badness = max(times.values())/ min(times.values())
        #         # data.append((ig_query.duration, badness, f"{'L' if ig_query.data['rationale'] == 'learning' else 'H'} {ig_query.instance} {ig_query.duration:0.3f}"))
        #         # print(f"{'L' if ig_query.data['rationale'] == 'learning' else 'H'} {ig_query.instance} {ig_query.duration:0.3f}", list(times.items()))

        #     # for (duration, badness, description) in sorted(data):
        #         # print(f"{description} {badness:0.2f}")

        #     total = 0.0
        #     for push in trace.descendants('Push'):
        #         total += push.duration
        #     print(f"Total pushing time {total}")

        #     total = 0.0
        #     for ig in trace.descendants('IG'):
        #         if ig.data['rationale'] == 'learning':
        #             total += ig.duration
        #     print(f"Total learning time {total}")

            

        def print_frames(lemmas: Dict, frames: Dict) -> None:
            frame_numbers, bad_lemmas, safeties, initial_conditions = frames['frame_numbers'], frames['bad_lemmas'], frames['safeties'], frames['initial_conditions']
            print ("[IC3] ---- Frame summary")
            for frame_num, index in sorted(zip(frame_numbers, range(len(lemmas))), key = lambda x: IC3Frames.frame_key(x[0])):
                if frame_num == 0 and index in bad_lemmas:
                    continue
                code = '$' if index in safeties else 'i' if index in initial_conditions else 'b' if index in bad_lemmas else ' '
                fn_str = f"{frame_num:2}" if frame_num is not None else ' +'
                print(f"[IC3] lemma {fn_str} {code} {lemmas[index]}")
            print("[IC3] ----")
            if frames['elapsed'] is not None:
                print(f"time: {frames['elapsed']:0.3f}")

        async def check_frame_redundancy(lemmas: Dict, frames: Dict, frame_number: IC3Frames.FrameNum) -> None:
            frame = [i for i in range(len(frames['frame_numbers'])) if IC3Frames.frame_leq(frame_number, frames['frame_numbers'][i])]
            print("frame is", len(frame), "lemmas")
            checker = AdvancedChecker(syntax.the_program, log=open("/dev/null", 'w'))
            for i in frame:
                for j in frame:
                    if i == j: continue
                    result = await checker.check_implication([lemmas[i]], lemmas[j], parallelism=5, timeout=100)
                    if result.result == SatResult.unsat:
                        print(f"{lemmas[i]} -> {lemmas[j]}")
                    else:
                        pass
                        #print(f"{i:3d} ?? {j:3d}")

        async def check_frame_redundancy2(lemmas: Dict, frames: Dict, frame_number: IC3Frames.FrameNum) -> None:
            orig_frame = [i for i in range(len(frames['frame_numbers'])) if IC3Frames.frame_leq(frame_number, frames['frame_numbers'][i])]
            frame = set(orig_frame)
            print("frame is", len(frame), "lemmas")
            checker = AdvancedChecker(syntax.the_program, log=open("/dev/null", 'w'))
            for i in orig_frame:
                if i not in frame: continue
                result = await checker.check_implication([lemmas[j] for j in frame if i != j], lemmas[i], parallelism=2, timeout=100)
                if result.result == SatResult.unsat:
                    print(lemmas[i], "is redundant")
                    frame.remove(i)
            print("\nFinal frame", frame_number if frame_number is not None else 'inf')
            for i in sorted(frame):
                print(lemmas[i])
            print(f"trimmed {len(orig_frame) - len(frame)} lemmas of {len(orig_frame)}")

        async def check_frame_redundancy3(lemmas: Dict, frames: Dict) -> None:
            frame_numbers, bad_lemmas, safeties, initial_conditions = frames['frame_numbers'], frames['bad_lemmas'], frames['safeties'], frames['initial_conditions']
            redundancy_frames = set()
            checker = AdvancedChecker(syntax.the_program, log=open("/dev/null", 'w'))

            for index in sorted(range(len(frame_numbers)), key = lambda x: IC3Frames.frame_key(frame_numbers[x]), reverse=True):
                orig_frame = [i for i in range(len(frame_numbers)) if IC3Frames.frame_leq(frame_numbers[index], frame_numbers[i]) and i not in redundancy_frames]
                result = await checker.check_implication([lemmas[j] for j in orig_frame if index != j], lemmas[index], parallelism=2, timeout=100)
                if result.result == SatResult.unsat:
                    # print(lemmas[index], "is redundant")
                    redundancy_frames.add(index)

            for frame_num, index in sorted(zip(frame_numbers, range(len(lemmas))), key = lambda x: IC3Frames.frame_key(x[0])):
                fn_str = f"{frame_num:2}" if frame_num is not None else ' +'
                code = '$' if index in safeties else 'r' if index in redundancy_frames else 'i' if index in initial_conditions else 'b' if index in bad_lemmas else  ' '
                print(f"lemma {fn_str} {code} {lemmas[index]}")

        async def check_golden_invariant(lemmas: Dict, frames: Dict) -> None:
            golden_invariant = [e.expr for e in syntax.the_program.invs()]
            checker = AdvancedChecker(syntax.the_program, log=open("/dev/null", 'w'))

            frame_numbers, bad_lemmas, safeties, initial_conditions = frames['frame_numbers'], frames['bad_lemmas'], frames['safeties'], frames['initial_conditions']
            for frame_num, index in sorted(zip(frame_numbers, range(len(lemmas))), key = lambda x: IC3Frames.frame_key(x[0])):
                if frame_num == 0 and index in bad_lemmas:
                    continue
                code = '$' if index in safeties else 'i' if index in initial_conditions else 'b' if index in bad_lemmas else ' '
                fn_str = f"{frame_num:2}" if frame_num is not None else ' +'
                result = await checker.check_implication(golden_invariant, lemmas[index], parallelism=5, timeout=100)
                imp = ">>" if result.result == SatResult.unsat else '  '
                print(f"lemma {fn_str} {code} {imp} {lemmas[index]}")

        def find_frame_by_time(time: float) -> Dict:
            found = {}
            for frame in frames:
                if frame['elapsed'] is not None and frame['elapsed'] < time:
                    found = frame
            return found

        frame_of_interest = find_frame_by_time(100000)
        # print_frames(lemmas, frame_of_interest)
        print("\nFrame redundancy:")
        await check_frame_redundancy3(lemmas, frame_of_interest)
        # print("\nGolden invariant implication:")
        print("\nImplied by human invariant:")
        await check_golden_invariant(lemmas, frame_of_interest)
    asyncio.run(main())

def extract_vmt(_: Solver) -> None:
    prog = syntax.the_program
    scope = cast(Scope[str], prog.scope)

    def to_smtlib(expr: Expr) -> str:
        if isinstance(expr, syntax.Bool):
            return "true" if expr.val else "false"
        elif isinstance(expr, syntax.Int):
            assert False, "Integers not supported"
        elif isinstance(expr, UnaryExpr) and expr.op == 'NEW':
            assert scope.new_allowed()
            with scope.next_state_index():
                return to_smtlib(expr.arg)
        elif isinstance(expr, UnaryExpr):
            arg = to_smtlib(expr.arg)
            if expr.op == 'NOT':
                return f"(not {arg})"
            assert False
        elif isinstance(expr, BinaryExpr):
            a, b = to_smtlib(expr.arg1), to_smtlib(expr.arg2)
            if expr.op == 'IMPLIES':
                return f"(=> {a} {b})"
            if expr.op == 'IFF':
                return f"(= {a} {b})"
            if expr.op == 'EQUAL':
                return f"(= {a} {b})"
            if expr.op == 'NOTEQ':
                return f"(not (= {a} {b}))"
            assert False
        elif isinstance(expr, NaryExpr):
            args = ' '.join(to_smtlib(arg) for arg in expr.args)
            if expr.op == 'AND':
                return f"(and {args})"
            if expr.op == 'OR':
                return f"(or {args})"
            if expr.op == 'DISTINCT':
                return f"(distinct {args})"
            assert False

        elif isinstance(expr, AppExpr):
            d = scope.get(expr.callee)
            if isinstance(d, DefinitionDecl):
                assert False, "definitions not supported"
            elif isinstance(d, (syntax.RelationDecl, syntax.FunctionDecl)):
                args = ' '.join(to_smtlib(arg) for arg in expr.args)
                callee = f"__{d.name}" if d.mutable and scope.current_state_index == 0 else d.name
                return f"({callee} {args})"
            else:
                assert False, f'{d}\n{expr}'

        elif isinstance(expr, QuantifierExpr):
            bvs = ' '.join(f"({b.name} {syntax.get_decl_from_sort(b.sort).name})" for b in expr.binder.vs)
            with scope.in_scope(expr.binder, [b.name for b in expr.binder.vs]):
                e = to_smtlib(expr.body)

            return f"({'forall' if expr.quant == 'FORALL' else 'exists'} ({bvs}) {e})"

        elif isinstance(expr, syntax.Id):
            d = scope.get(expr.name)
            assert d is not None, f'{expr.name}\n{expr}'
            if isinstance(d, (syntax.RelationDecl, syntax.ConstantDecl)):
                return f"__{d.name}" if d.mutable and scope.current_state_index == 0 else d.name
            elif isinstance(d, DefinitionDecl):
                assert False
            else:
                assert not isinstance(d, syntax.FunctionDecl)  # impossible since functions have arity > 0
                e, = d
                return e
        elif isinstance(expr, IfThenElse):
            return f"(ite {to_smtlib(expr.branch)} {to_smtlib(expr.then)} {to_smtlib(expr.els)})"
        elif isinstance(expr, Let):
            assert False, "let not supported"
        else:
            assert False, expr


    with open(utils.args.output, 'w') as outfile:
        outfile.write(f"; VMT translation of {utils.args.filename} (IC3PO flavored)")

        outfile.write("\n")
        for sort in prog.sorts():
            outfile.write(f"(declare-sort {sort.name} 0)\n")

        outfile.write("\n")
        for sort in prog.sorts():
            size = 1
            outfile.write(f"(define-fun .{sort.name} ((S {sort.name})) {sort.name} (! S :sort {size}))\n")

        outfile.write("\n")
        for const in prog.constants():
            if const.mutable:
                outfile.write(f"(declare-fun __{const.name} () {syntax.get_decl_from_sort(const.sort).name})\n")
        for rel in prog.relations():
            if rel.mutable:
                rel_args = ' '.join(syntax.get_decl_from_sort(s).name for s in rel.arity)
                outfile.write(f"(declare-fun __{rel.name} ({rel_args}) Bool)\n")
        for func in prog.functions():
            if func.mutable:
                func_args = ' '.join(syntax.get_decl_from_sort(s).name for s in func.arity)
                outfile.write(f"(declare-fun __{func.name} ({func_args}) {syntax.get_decl_from_sort(func.sort).name})\n")

        outfile.write("\n")
        for const in prog.constants():
            if const.mutable:
                outfile.write(f"(declare-fun {const.name} () {syntax.get_decl_from_sort(const.sort).name})\n")
        for rel in prog.relations():
            if rel.mutable:
                rel_args = ' '.join(syntax.get_decl_from_sort(s).name for s in rel.arity)
                outfile.write(f"(declare-fun {rel.name} ({rel_args}) Bool)\n")
        for func in prog.functions():
            if func.mutable:
                func_args = ' '.join(syntax.get_decl_from_sort(s).name for s in func.arity)
                outfile.write(f"(declare-fun {func.name} ({func_args}) {syntax.get_decl_from_sort(func.sort).name})\n")

        outfile.write("\n")
        for const in prog.constants():
            if const.mutable:
                outfile.write(f"(define-fun .{const.name} () {syntax.get_decl_from_sort(const.sort).name} (! __{const.name} :next {const.name}))\n")
        for rel in prog.relations():
            if rel.mutable:
                rel_decl_args = ' '.join(f"(V{i} {syntax.get_decl_from_sort(s).name})" for i, s in enumerate(rel.arity))
                rel_args = ' '.join(f"V{i}" for i, s in enumerate(rel.arity))
                rel_call = f"__{rel.name}" if len(rel.arity) == 0 else f"(__{rel.name} {rel_args})"
                outfile.write(f"(define-fun .{rel.name} ({rel_decl_args}) Bool (! {rel_call} :next {rel.name}))\n")
        for func in prog.functions():
            if func.mutable:
                func_decl_args = ' '.join(f"(V{i} {syntax.get_decl_from_sort(s).name})" for i, s in enumerate(func.arity))
                func_args = ' '.join(f"V{i}" for i, s in enumerate(func.arity))
                outfile.write(f"(define-fun .{func.name} ({func_decl_args}) {syntax.get_decl_from_sort(func.sort).name} (! (__{func.name} {func_args}) :next {func.name}))\n")

        outfile.write("\n")
        for const in prog.constants():
            if not const.mutable:
                outfile.write(f"(declare-fun {const.name} () {syntax.get_decl_from_sort(const.sort).name})\n")
        for rel in prog.relations():
            if not rel.mutable:
                rel_args = ' '.join(syntax.get_decl_from_sort(s).name for s in rel.arity)
                outfile.write(f"(declare-fun {rel.name} ({rel_args}) Bool)\n")
        for func in prog.functions():
            if not func.mutable:
                func_args = ' '.join(syntax.get_decl_from_sort(s).name for s in func.arity)
                outfile.write(f"(declare-fun {func.name} ({func_args}) {syntax.get_decl_from_sort(func.sort).name})\n")


        outfile.write("\n")
        for const in prog.constants():
            if not const.mutable:
                outfile.write(f"(define-fun .{const.name} () {syntax.get_decl_from_sort(const.sort).name} (! {const.name} :global true))\n")
        for rel in prog.relations():
            if not rel.mutable:
                rel_decl_args = ' '.join(f"(V{i} {syntax.get_decl_from_sort(s).name})" for i, s in enumerate(rel.arity))
                rel_args = ' '.join(f"V{i}" for i, s in enumerate(rel.arity))
                rel_call = rel.name if len(rel.arity) == 0 else f"({rel.name} {rel_args})"
                outfile.write(f"(define-fun .{rel.name} ({rel_decl_args}) Bool (! {rel_call} :global true))\n")
        for func in prog.functions():
            if not func.mutable:
                func_decl_args = ' '.join(f"(V{i} {syntax.get_decl_from_sort(s).name})" for i, s in enumerate(func.arity))
                func_args = ' '.join(f"V{i}" for i, s in enumerate(func.arity))
                outfile.write(f"(define-fun .{func.name} ({func_decl_args}) {syntax.get_decl_from_sort(func.sort).name} (! ({func.name} {func_args}) :global true))\n")


        for rel in prog.derived_relations():
            ax = rel.derived_axiom
            assert ax is not None
            assert rel.mutable
            outfile.write(f"""\n(define-fun .def___{rel.name} () Bool (!
 (let (($v {to_smtlib(ax)}
 ))
 (and $v))
 :definition __{rel.name}))""")
            with scope.n_states(2):
                outfile.write(f"""\n(define-fun .def_{rel.name} () Bool (!
 (let (($v {to_smtlib(New(ax))}
 ))
 (and $v))
 :definition {rel.name}))""")

        safeties = to_smtlib(syntax.And(*(inv.expr for inv in prog.safeties())))
        outfile.write(f"""\n(define-fun .prop () Bool (!
 (let (($v {safeties}
 ))
 (and $v))
 :invar-property 0))\n""")

        inits = to_smtlib(syntax.And(*(inv.expr for inv in prog.inits())))
        outfile.write(f"""\n(define-fun .init () Bool (!
 (let (($v {inits}
 ))
 (and $v))
 :init true))\n""")

        axioms = to_smtlib(syntax.And(*(ax.expr for ax in prog.axioms())))
        outfile.write(f"""\n(define-fun .axiom () Bool (!
 (let (($v {axioms}
 ))
 (and $v))
 :axiom true))\n""")

        for tr in prog.transitions():
            expr = tr.as_twostate_formula(prog.scope)
            with scope.n_states(2):
                outfile.write(f"""\n(define-fun .action_{tr.name} () Bool (!
    (let (($v {to_smtlib(expr)}
    ))
    (and $v))
    :action {tr.name}))\n""")


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
    s.add_argument("--epr-edges", dest="epr_edges", type=epr_edges, default=[], help="Allowed EPR edges in inferred formula")
    s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: x.split(','), default=[], action='extend', help="Experimental flags")
    s.add_argument("--log-dir", dest="log_dir", type=str, default="", help="Log directory")
    s.add_argument("--cpus", dest="cpus", type=int, default=10, help="CPU threads to use (best effort only)")
    result.append(s)

    s = subparsers.add_parser('fol-extract', help='Extract conjuncts to a file')
    s.set_defaults(main=fol_extract)
    s.add_argument("--logic", choices=('fol', 'epr', 'universal'), default="fol", help="Restrict form of separators to given logic (fol is unrestricted)")
    s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: x.split(','), default=[], action='extend', help="Experimental flags")
    s.add_argument("--output", type=str, help="Output to file")
    result.append(s)

    s = subparsers.add_parser('fol-learn', help='Learn a given formula')
    s.set_defaults(main=fol_learn)
    s.add_argument("--logic", choices=('fol', 'epr', 'universal'), default="fol", help="Restrict form of separators to given logic (fol is unrestricted)")
    s.add_argument("--index", dest="index", type=int, default=-1, help="Invariant index")
    s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: x.split(','), default=[], action='extend', help="Experimental flags")
    s.add_argument("--log-dir", dest="log_dir", type=str, default="", help="Log directory")
    result.append(s)

    s = subparsers.add_parser('fol-benchmark-solver', help='Test SMT solver backend')
    s.set_defaults(main=fol_benchmark_solver)
    s.add_argument("--query", type=str, help="Query to benchmark")
    s.add_argument("--output", type=str, help="Output to file")
    s.add_argument("--epr-edges", dest="epr_edges", type=epr_edges, default=[], help="Allowed EPR edges in inferred formula")
    s.add_argument("--log-dir", dest="log_dir", type=str, default="", help="Log directory")
    s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: x.split(','), default=[], action='extend', help="Experimental flags")
    result.append(s)

    s = subparsers.add_parser('fol-benchmark-ig', help='Test IG query solver')
    s.set_defaults(main=fol_benchmark_ig)
    s.add_argument("--query", type=str, help="Query to benchmark")
    s.add_argument("--output", type=str, help="Output to file")
    s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: x.split(','), default=[], action='extend', help="Experimental flags")
    s.add_argument("--log-dir", dest="log_dir", type=str, default="", help="Log directory")
    s.add_argument("--logic", choices=('fol', 'epr', 'universal'), default="fol", help="Restrict form of separators to given logic (fol is unrestricted)")
    s.add_argument("--epr-edges", dest="epr_edges", type=epr_edges, default=[], help="Allowed EPR edges in inferred formula")
    result.append(s)

    s = subparsers.add_parser('fol-benchmark-eval', help='Test formula evaluation performance')
    s.set_defaults(main=fol_benchmark_eval)
    s.add_argument("--query", type=str, help="Query to benchmark")
    s.add_argument("--output", type=str, help="Output to file")
    s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: x.split(','), default=[], action='extend', help="Experimental flags")
    result.append(s)

    s = subparsers.add_parser('fol-debug-ig', help='Debug a IG solution')
    s.set_defaults(main=fol_debug_ig)
    s.add_argument("--query", type=str, help="Solution to query")
    s.add_argument("--epr-edges", dest="epr_edges", type=epr_edges, default=[], help="Allowed EPR edges in inferred formula")
    s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: x.split(','), default=[], action='extend', help="Experimental flags")
    s.add_argument("--log-dir", dest="log_dir", type=str, default="", help="Log directory")
    # s.add_argument("--output", type=str, help="Output to file")
    result.append(s)

    s = subparsers.add_parser('fol-debug-frames', help='Debug a frame set')
    s.set_defaults(main=fol_debug_frames)
    s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: x.split(','), default=[], action='extend', help="Experimental flags")
    s.add_argument("--log-dir", dest="log_dir", type=str, default="", help="Log directory")
    # s.add_argument("--output", type=str, help="Output to file")
    result.append(s)

    s = subparsers.add_parser('extract-vmt', help='Extract a .vmt file')
    s.set_defaults(main=extract_vmt)
    s.add_argument("--output", required=True, type=str, help="Output to file")
    result.append(s)

    return result
