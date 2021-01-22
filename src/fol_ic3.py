

from dataclasses import dataclass
from typing import Any, Callable, DefaultDict, Dict, Generator, Iterable, Iterator, Sequence, TextIO, List, Optional, Set, Tuple, Union, cast, Counter as CounterType, get_origin

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
import shutil
from collections import Counter, defaultdict

import z3
from async_tools import AsyncConnection, ScopedProcess, ScopedTasks
from semantics import State
import separators
from typechecker import typecheck_expr
from translator import Z3Translator, quantifier_alternation_graph
import utils
from logic import Diagram, Expr, Solver, Trace
import syntax
from syntax import BinaryExpr, BoolSort, DefinitionDecl, Exists, Forall, IfThenElse, InvariantDecl, Let, NaryExpr, New, Not, Program, QuantifierExpr, Scope, SortedVar, UnaryExpr, UninterpretedSort
from fol_trans import eval_predicate, formula_to_predicate, predicate_to_formula, prog_to_sig, state_to_model
from separators import Constraint, Neg, Pos, Imp
from separators.separate import FixedImplicationSeparator, FixedImplicationSeparatorPyCryptoSat, Logic, PrefixConstraints, PrefixSolver
import networkx

async def _robust_check(formulas: Sequence[Callable[[Solver, Z3Translator], None]], n_states: int = 1, parallelism: int = 1, timeout: float = 0.0, log: TextIO = sys.stdout, prefix: str = '') -> Union[Trace, z3.CheckSatResult]:
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
        t2 = s_cvc4.get_translator(n_states)
        while True:
            try:
                (f_i, count, use_cvc4, time_limit) = cast(Tuple[int, int, bool, float], await conn.recv())
            except EOFError:
                return
            s = s_cvc4 if use_cvc4 else s_z3
            with s.new_frame():
                formulas[f_i](s, t2 if use_cvc4 else t)
                # print(f"{prefix} _robust_check(): checking ({f_i}, {count}, {use_cvc4}) in {time_limit}", file=log)
                # print(s.assertions())
                r = s.check(timeout = min(1000000000, int(time_limit * 1000)))
                # print(f"{prefix} _robust_check(): r = {r}", file=log)
                if not use_cvc4 and r == z3.sat:
                    print(f"{prefix} transmuting z3 sat->unknown", file=log)
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
                print(f"{prefix} attempt (F_{v[0]} i={v[1]} {'cvc4' if v[2] else 'z3'} to={v[3]}) returned {z3.sat if isinstance(r, Trace) else r} in {end-start:0.3f}", file=log)
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

_robust_id = 0
def _get_robust_id() -> str:
    global _robust_id
    id = f'{_robust_id:06d}'
    _robust_id += 1
    return id

async def robust_check_transition(old_hyps: Iterable[Expr], new_conc: Expr, minimize: Optional[bool] = None, transition: Optional[DefinitionDecl] = None, parallelism:int = 1, timeout: float = 0.0, log: TextIO = sys.stdout) -> Union[Trace, z3.CheckSatResult]:
    id = _get_robust_id()
    log_prefix = f'[Tr-{id}]'
    start = time.time()
    r: Union[Trace, z3.CheckSatResult, None] = None
    try:
        def make_formula(s: Solver, t: Z3Translator, transition: DefinitionDecl) -> None:
            for e in [New(Not(new_conc)), transition.as_twostate_formula(syntax.the_program.scope)]:
                s.add(t.translate_expr(e))
            exprs = list(old_hyps)
            random.shuffle(exprs)
            for e in exprs:
                s.add(t.translate_expr(e))
        formulas = [(lambda s, t, trans=transition: make_formula(s, t, trans)) for transition in syntax.the_program.transitions()]
        r = await _robust_check(formulas, 2, parallelism=parallelism, timeout=timeout, log=log, prefix=log_prefix)
        return r
    finally:
        elapsed = time.time() - start
        res = 'unsat' if r == z3.unsat else 'sat' if isinstance(r, Trace) else 'unk' if r == z3.unknown else 'int'
        if elapsed > 5 and utils.args.log_dir != '':
            fname = f'tr-query-{id}-{res}-{int(elapsed):04d}.pickle'
            with open(os.path.join(utils.args.log_dir, 'smt-queries', fname), 'wb') as f:
                pickle.dump((old_hyps, new_conc, minimize, transition.name if transition is not None else None), f, protocol=pickle.HIGHEST_PROTOCOL)
            print(log_prefix, f'transition query result {res} took {elapsed:0.3f} log {fname}', file=log)
        else:
            print(log_prefix, f'transition query result {res} took {elapsed:0.3f}', file=log)

async def robust_check_implication(hyps: Iterable[Expr], conc: Expr, minimize: Optional[bool] = None, parallelism:int = 1, timeout: float = 0.0, log: TextIO = sys.stdout) -> Union[Trace, z3.CheckSatResult]:
    id = _get_robust_id()
    log_prefix = f'[Im-{id}]'
    start = time.time()
    r: Union[Trace, z3.CheckSatResult, None] = None
    try:
        def make_formula(s: Solver, t: Z3Translator) -> None:
            s.add(t.translate_expr(Not(conc)))
            hs = list(hyps)
            random.shuffle(hs)
            for h in hs:
                s.add(t.translate_expr(h))
        r = await _robust_check([make_formula], 1, parallelism=parallelism, timeout=timeout, log=log, prefix=log_prefix)
        return r
    finally:
        elapsed = time.time() - start
        res = 'unsat' if r == z3.unsat else 'sat' if isinstance(r, Trace) else 'unk' if r == z3.unknown else 'int'
        if elapsed > 5 and utils.args.log_dir != '':
            fname = f'im-query-{id}-{res}-{int(elapsed):04d}.pickle'
            with open(os.path.join(utils.args.log_dir, 'smt-queries', fname), 'wb') as f:
                pickle.dump((hyps, conc, minimize), f, protocol=pickle.HIGHEST_PROTOCOL)
            print(log_prefix, f'implication query result {res} took {elapsed:0.3f} log {fname}', file=log)
        else:
            print(log_prefix, f'implication query result {res} took {elapsed:0.3f}', file=log)


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

def _log_ig_problem(name:str, rationale: str, block: Neg, pos: List[Constraint], states: Union[List[State], Dict[int, State]], prior_frame: List[Expr], golden: List[InvariantDecl]) -> None:
    if utils.args.log_dir == '': return
    with open(os.path.join(utils.args.log_dir, 'ig-problems', f'{name}.pickle'), 'wb') as f:
        pickle.dump((rationale, block, pos, {i: states[i] for c in [block, *pos] for i in c.states()}, prior_frame, golden), f)

def _log_sep_problem(name: str, prefix: Tuple[Tuple[Optional[bool], int], ...], constraints: List[Constraint], states: Union[List[State], Dict[int, State]], prior_frame: List[Expr]) -> None:
    if utils.args.log_dir == '': return
    with open(os.path.join(utils.args.log_dir, 'sep-problems', f'{name}.pickle'), 'wb') as f:
        pickle.dump((prefix, constraints, {i: states[i] for c in constraints for i in c.states()}, prior_frame), f)
    
def _log_sep_unsep(name: str, prefix: Tuple[Tuple[Optional[bool], int], ...], constraints: List[Constraint], states: Union[List[State], Dict[int, State]]) -> None:
    if utils.args.log_dir == '': return
    with open(os.path.join(utils.args.log_dir, 'sep-unsep', f'{name}.pickle'), 'wb') as f:
        pickle.dump((prefix, constraints, {i: states[i] for c in constraints for i in c.states()}), f)
    

class Logging:
    def __init__(self, log_dir: str) -> None:
        self._log_dir = log_dir
        self._sep_log: TextIO = open('/dev/null', 'w') if log_dir == '' else open(os.path.join(utils.args.log_dir, 'sep.log'), 'w', buffering=1)
        self._smt_log: TextIO = open('/dev/null', 'w') if log_dir == '' else open(os.path.join(utils.args.log_dir, 'smt.log'), 'w', buffering=1)
        self._ig_log: TextIO  = sys.stdout if log_dir == '' else open(os.path.join(utils.args.log_dir, 'ig.log'),  'w', buffering=1)

class IGSolver:
    def __init__(self, state: State, positive: List[State], frame: List[Expr], logs: Logging, prog: Program, rationale: str, identity: int):
        self._sig = prog_to_sig(prog)
        self._logs = logs
        
        # Logging
        self._identity = identity
        self._log_prefix = f"[{rationale[0].upper()}({identity})]"
        self._sep_problem_index = 0
        
        # A list of states local to this IG query. All constraints are w.r.t. this list
        self._states: List[State] = []
        self._states_pickled: List[bytes] = []
        
        self._local_eval_cache: Dict[Tuple[int, int], bool] = {}

        self._frame = frame
        self._prefix_solver = PrefixSolver(self._sig)
        
        self._necessary_constraints: Set[Constraint] = set([Neg(self.add_local_state(state))]) # This is just Neg(0), the state to block
        self._constraints_in_frame: Set[Constraint] = set(self._necessary_constraints) # This is all constraints that satisfy the prior frame
        self._unsep_constraints: Set[Constraint] = set(self._necessary_constraints) # Constraints that are part of some unsep core, eliminating some prefix(es)
        self._popularity: CounterType[Constraint] = Counter() # Constraints that have shown to be useful in unsep cores
        self._popularity_total = 0
        # Seed the popular constraints with known positive states
        for pos_state in positive:
            c = Pos(self.add_local_state(pos_state))
            self._constraints_in_frame.add(c)
            self._popularity[c] = 1
        for n in self._necessary_constraints:
            self._popularity[n] = 2
        self._MAX_POPULAR = 150

    def local_eval(self, pred: int, local_state: int) -> bool:
        if (pred, local_state) not in self._local_eval_cache:
            self._local_eval_cache[(pred, local_state)] = eval_predicate(self._states[local_state], self._frame[pred])
        return self._local_eval_cache[(pred, local_state)]

    def add_local_state(self, s: State) -> int:
        self._states.append(s)
        self._states_pickled.append(pickle.dumps(s, pickle.HIGHEST_PROTOCOL))
        return len(self._states) - 1
    
    def _print(self, *args: Any, end: str='\n') -> None:
        print(self._log_prefix, *args, file=self._logs._ig_log, end=end)

    async def IG2_worker(self, conn: AsyncConnection) -> None:
        sys.stdout = self._logs._sep_log
        print("Started Worker")
        prog = syntax.the_program
        sep = FixedImplicationSeparatorPyCryptoSat(self._sig, (), PrefixConstraints(), 0, set(), [])
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
                (prefix, pc) = v['prefix']
                del sep
                sep = FixedImplicationSeparatorPyCryptoSat(self._sig, prefix, pc, 1, set(), [])
                sep_constraints = set()
                sep_constraints_order = []
                mapping = {}
                sep_time, eval_time = 0.0, 0.0
            if 'constraints' in v:
                (cons, extra_states) = v['constraints']
                states.update((i, pickle.loads(p)) for i,p in extra_states.items())
                constraints = list(cons)
            if 'block_last_separator' in v:
                sep.block_last_separator()
            if 'sep' in v:
                minimized = False
                while True:
                    print(f"Separating with prefix {prefix}")
                    start = time.time()
                    sep_r = sep.separate(minimize=minimized)
                    sep_time += time.time() - start
                    if sep_r is None:
                        print(f"UNSEP |core|={len(sep_constraints)} in (sep {sep_time:0.3f}, eval {eval_time:0.3f})")
                        await conn.send({'unsep': sep_constraints_order})
                        break

                    with prog.scope.n_states(1):
                        p = formula_to_predicate(sep_r, prog.scope)
                    print(f"Internal candidate: {p}")
                    start = time.time()
                    for c in constraints:
                        if c in sep_constraints: continue
                        if not satisifies_constraint(c, p, states):
                            print(f"Adding internal constraint {c}")
                            for s in c.states():
                                if s not in mapping:
                                    mapping[s] = sep.add_model(state_to_model(states[s]))
                            sep.add_constraint(c.map(mapping))
                            sep_constraints.add(c)
                            sep_constraints_order.append(c)
                            minimized = False
                            eval_time += time.time() - start
                            break
                    else:
                        eval_time += time.time() - start
                        # All known constraints are satisfied
                        if not minimized:
                            minimized = True
                            continue # continue the loop, now asking for a minimized separator
                        else:
                            print(f"Satisfied with {p} in (sep {sep_time:0.3f}, eval {eval_time:0.3f})")
                            await conn.send({'candidate': p, 'constraints': sep_constraints_order})
                            break
    async def solve(self, n_threads: int = 1) -> Optional[Expr]:
        # _log_ig_problem(identity, rationale, Neg(0), list(constraints_in_frame), states, [self._predicates[i] for i in frame_preds], [inv for inv in syntax.the_program.invs()])

        solution: asyncio.Future[Optional[Expr]] = asyncio.Future()

        async def check_candidate(p: Expr) -> Union[Constraint, z3.CheckSatResult]:
            # F_0 => p?
            initial_state = await robust_check_implication([init.expr for init in syntax.the_program.inits()], p, minimize='no-minimize-cex' not in utils.args.expt_flags, log=self._logs._smt_log)
            if isinstance(initial_state, Trace):
                self._print("Adding initial state")
                return Pos(self.add_local_state(initial_state.as_state(0)))
            elif initial_state == z3.unknown:
                self._print("Warning, implication query returned unknown")
            
            # F_i-1 ^ p => wp(p)?
            edge = await robust_check_transition([p, *self._frame], p, minimize='no-minimize-cex' not in utils.args.expt_flags, parallelism = 2, timeout=500, log=self._logs._smt_log)

            if isinstance(edge, Trace):
                self._print(f"Adding edge")
                return Imp(self.add_local_state(edge.as_state(0)), self.add_local_state(edge.as_state(1)))
            return z3.unsat if edge == z3.unsat and initial_state == z3.unsat else z3.unknown

        async def generalize_quantifiers(p: Expr, constraints: Set[Constraint]) -> Expr:
            prefix, matrix = decompose_prenex(p)
            self._print(f"Original prefix {prefix}, matrix {matrix}")
            #assert prefix_in_epr(prefix)
            while True:
                for new_prefix in generalizations_of_prefix(prefix):
                    assert new_prefix != prefix
                    if not prefix_in_epr(new_prefix) and 'generalize-non-epr' not in utils.args.expt_flags:
                        self._print(f"Not in EPR")
                        continue
                    q = compose_prenex(new_prefix, matrix)
                    self._print(f"Trying... {q}")
                    if all(satisifies_constraint(c, q, self._states) for c in constraints):
                        self._print("Passed constraints")
                        new_constr = await check_candidate(q)
                        if new_constr == z3.unsat:
                            self._print("Accepted new formula")
                            prefix = new_prefix
                            break
                        elif isinstance(new_constr, Constraint):
                            constraints.add(new_constr)
                        self._print("Not relatively inductive")
                    else:
                        self._print("Rejected by constraints")
                else:
                    break
            return compose_prenex(prefix, matrix)

        async def worker_handler(pc: PrefixConstraints) -> None:
            with ScopedProcess(self.IG2_worker) as conn:
                # Keep track of which states the worker knows about, so we only send necessary ones
                worker_known_states: Set[int] = set()
                def send_constraints(cs: List[Constraint]) -> Tuple[List[Constraint], Dict[int, bytes]]:
                    new_states = set(s for c in cs for s in c.states()).difference(worker_known_states)
                    extra_states = {i: self._states_pickled[i] for i in new_states}
                    worker_known_states.update(new_states)
                    # print(f"Constraints are: {cs}")
                    return (cs, extra_states)

                while True:
                    # Get a prefix from the solver
                    # feasible = prefix_solver.is_feasible(unsep_constraints, ((True, 'inst'), (True, 'quorum'), (True, 'round'), (True, 'round'), (True, 'value'), (False, 'node')))
                    # self._print(f"Is Feasible: {feasible}")
                    pre = self._prefix_solver.get_prefix(self._unsep_constraints, pc)
                    if pre is None:
                        return
                    pre_pp = " ".join(('A' if fa == True else 'E' if fa == False else 'Q') + self._sig.sort_names[sort_i] + '.' for (fa, sort_i) in pre)
                    self._print(f"Trying: {pre_pp}")
                    reservation = self._prefix_solver.reserve(pre, pc)
                    await conn.send({'prefix': (pre, pc)})
                    pop = [c for c, cnt in self._popularity.most_common(self._MAX_POPULAR)]
                    last_sep_constraints : Set[Constraint] = set()
                    next_constraints = list(self._necessary_constraints) + pop
                    _log_sep_problem(f"ig-{self._identity}-{self._sep_problem_index}", pre, next_constraints, self._states, self._frame)
                    while True:
                        if solution.done(): return
                        await conn.send({'constraints': send_constraints(next_constraints), 'sep': None})
                        v = await conn.recv()
                        if 'candidate' in v:
                            p, sep_constraints = cast(Expr, v['candidate']), cast(List[Constraint], v['constraints'])
                            # new_constraint = check_popular_constraints(set(current_constraints), p)
                            # if new_constraint is not None:
                            #     self._print("Using popular constraint")
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
                                if cons in self._necessary_constraints: continue
                                self._print("Using popular constraint")
                                self._popularity[cons] += 1
                                self._popularity_total += 1
                                if self._popularity_total == 2*self._MAX_POPULAR:
                                    self._popularity_total = 0
                                    for k in self._popularity.keys():
                                        self._popularity[k] = (self._popularity[k] * 5) // 6
                            last_sep_constraints = set_sep_constraints

                            if len(last_sep_constraints) > 100 and 'constraint-limiting' in utils.args.expt_flags:
                                new_constraint_result: Union[Constraint, z3.CheckSatResult] = z3.unknown
                                self._print(f"Used more than 100 constraints")
                            else:
                                new_constraint_result = await check_candidate(p)
                                if new_constraint_result == z3.unknown:
                                    self._print(f"Solver returned unknown ({p})")
                                    await conn.send({'block_last_separator': None})
                                    continue

                            if isinstance(new_constraint_result, Constraint):
                                # print(f"Adding {new_constraint}")
                                #current_constraints.append(new_constraint)
                                self._constraints_in_frame.add(new_constraint_result)
                                self._popularity[new_constraint_result] = self._popularity.most_common(self._MAX_POPULAR//2)[-1][1] + 1
                                self._popularity_total += 1
                                if self._popularity_total == 2*self._MAX_POPULAR:
                                    self._popularity_total = 0
                                    for k in self._popularity.keys():
                                        self._popularity[k] = (self._popularity[k] * 5) // 6
                                # if golden is not None:
                                #     if not satisifies_constraints([new_constraint], golden, states):
                                #         print(f"! -- oops {new_constraint} isn't satisfied by {golden}")

                                next_constraints = [new_constraint_result] + list(self._necessary_constraints) + [c for c, cnt in self._popularity.most_common(self._MAX_POPULAR)]
                                continue
                            elif new_constraint_result == z3.unsat:
                                if not solution.done():
                                    states_needed = set(s for c in sep_constraints for s in c.states())
                                    structs = dict((i, s) for i, s in enumerate(self._states) if i in states_needed)
                                    # if utils.args.log_dir != '':
                                    #     with open(os.path.join(utils.args.log_dir, f'ig-solutions/ig-solution-{self._log_prefix}.pickle'), 'wb') as output:
                                    #         pickle.dump({'states': structs, 'constraints': sep_constraints, 'solution': p, 'prior_frame': self._frame}, output)
                                    
                                    self._print(f"SEP with |constr|={len(sep_constraints)}")
                                    if 'no-generalize-quantifiers' not in utils.args.expt_flags:
                                        p = await generalize_quantifiers(p, set_sep_constraints)
                                    self._print(f"Learned {p}")
                                    solution.set_result(p)
                                return
                            elif new_constraint_result == z3.unknown:
                                core = sep_constraints
                                self._print(f"UNKNOWN: {pre_pp} ({pc.logic}) with |core|={len(core)}")
                                self._prefix_solver.unsep(core, pc, pre)
                                self._unsep_constraints.update(core)
                                break    

                        elif 'unsep' in v:
                            core = v['unsep']
                            self._print(f"UNSEP: {pre_pp} ({pc.logic}) with |core|={len(core)}")
                            _log_sep_unsep(f"ig-{self._identity}-{self._sep_problem_index}", pre, core, self._states)
                            # if False:
                            #     test_sep = FixedImplicationSeparator(sig, pre, pc)
                            #     m = {i: test_sep.add_model(state_to_model(states[i])) for i in range(len(states))}
                            #     for c in cs:
                            #         test_sep.add_constraint(c.map(m))
                            #     assert test_sep.separate() is None
                            self._prefix_solver.unsep(core, pc, pre)
                            # for c in core:
                            #     popularity[c] += 1
                            self._unsep_constraints.update(core)
                            break
                        else:
                            assert False
                    # print(f"Done with: {pre}")
                    self._prefix_solver.unreserve(reservation)

        # async def summary_logger() -> None:
        #     self._print(f"Inductive generalize blocking {state} in frame {frame} for {rationale}")
        #     st = self._states[state]
        #     size_summary = ', '.join(f"|{sort.name}|={len(elems)}" for sort, elems in st.univs.items())
        #     self._print(f"Size of state to block {size_summary}")
        #     n_formulas = 0
        #     for inv in syntax.the_program.invs():
        #         if st.eval(inv.expr) == False:
        #             cex = await robust_check_transition([*self._frame, inv.expr], inv.expr, minimize=False, timeout=500, log=self._logs._smt_log)
        #             ind_str = '(relatively inductive)' if cex == z3.unsat else '(not relatively inductive)' if isinstance(cex, Trace) else '(relatively inductive unknown)'
        #             self._print("golden formula is:", inv.expr, ind_str)
        #             n_formulas += 1
        #     self._print(f"Number of golden formula {n_formulas}")

        async def logger() -> None:
            query_start = time.time()
            while True:
                try: await asyncio.sleep(30)
                except asyncio.CancelledError:
                    if solution.done():
                        self._print(f"popularity: {self._popularity.most_common(self._MAX_POPULAR)}")
                    self._print(f"finished in: {time.time() - query_start:0.2f}s")
                    raise
                self._print(f"time: {time.time() - query_start:0.2f} sec constraints:{len(self._constraints_in_frame)}")

        if utils.args.logic == 'universal':
            pcs = [PrefixConstraints(Logic.Universal),
                   PrefixConstraints(Logic.Universal, max_repeated_sorts = 2),
                   PrefixConstraints(Logic.Universal, max_repeated_sorts = 3),
                   PrefixConstraints(Logic.Universal),
                   PrefixConstraints(Logic.Universal, max_repeated_sorts = 2),
                   PrefixConstraints(Logic.Universal, max_repeated_sorts = 3),]
        elif utils.args.logic == 'epr':
            pcs = [PrefixConstraints(Logic.Universal, max_repeated_sorts=2, max_depth=6),
                   PrefixConstraints(Logic.Universal, max_repeated_sorts=3, max_depth=6),
                   PrefixConstraints(Logic.EPR, max_alt=1, max_repeated_sorts=2, max_depth=6),
                   PrefixConstraints(Logic.EPR, max_alt=1, max_repeated_sorts=2, max_depth=6),
                   PrefixConstraints(Logic.EPR, max_alt=1, max_repeated_sorts=3, max_depth=6),
                   PrefixConstraints(Logic.EPR, max_alt=2, max_repeated_sorts=3, max_depth=6)]
                #    PrefixConstraints(Logic.EPR, min_depth=5, max_alt=1, max_repeated_sorts=2, max_depth=6),
                #    PrefixConstraints(Logic.EPR, min_depth=5, max_alt=2, max_repeated_sorts=3, max_depth=6)]
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
        multiplier = (n_threads + len(pcs) - 1)//len(pcs)

        async with ScopedTasks() as tasks:
            tasks.add(logger())
            # tasks.add(frame_updater())
            # tasks.add(summary_logger())
            # tasks.add(wait_blocked())
            # tasks.add(timeout())
            tasks.add(*(worker_handler(pc) for pc in pcs * multiplier))
            s = await solution
            self._print("Exiting IG_manager")
            return s




@dataclass(eq=True, frozen=True)
class Prefix:
    __slots__= ['quant_blocks', 'begin_forall']
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
    
    for depth_e in range(0, depth+1):
        for b in _gen(tuple(min(repeat, depth) for _ in range(sorts)), depth, alts, True, depth_e):
            yield Prefix(b, True)
    if not existentials: return
    for depth_e in range(0, depth+1):
        for b in _gen(tuple(min(repeat, depth) for _ in range(sorts)), depth, alts, False, depth_e):
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

class IGSolver2:
    def __init__(self, state: State, positive: List[State], frame: List[Expr], logs: Logging, prog: Program, rationale: str, identity: int):
        self._sig = prog_to_sig(prog)
        self._logs = logs
        
        # Logging
        self._rationale = rationale
        self._identity = identity
        self._log_prefix = f"[{rationale[0].upper()}({identity})]"
        self._sep_problem_index = 0
        
        # A list of states local to this IG query. All constraints are w.r.t. this list
        self._states: List[State] = []
        self._states_pickled_cache: List[bytes] = []

        # self._local_eval_cache: Dict[Tuple[int, int], bool] = {} # maps (predicate, state) to evaluation result

        self._frame = frame

        self._necessary_constraints: Set[Constraint] = set([Neg(self.add_local_state(state))]) # This is just Neg(0), the state to block
        self._reachable_constraints: Set[Constraint] = set([Pos(self.add_local_state(st)) for st in positive])
        
        # Prefix handling
        self._max_repeats = 4

        self._prefix_generators: Dict[Tuple[int, int], Iterator[Prefix]] = {} # maps (depth, alts) to a prefix generator
        self._unsep_cores: Dict[Prefix, List[Constraint]] = {}

        # logging etc:
        self._total_constraints_found: int = 0

    def _print(self, *args: Any, end: str='\n') -> None:
        print(self._log_prefix, *args, file=self._logs._ig_log, end=end)

    # def local_eval(self, pred: int, local_state: int) -> bool:
    #     if (pred, local_state) not in self._local_eval_cache:
    #         self._local_eval_cache[(pred, local_state)] = eval_predicate(self._states[local_state], self._frame[pred])
    #     return self._local_eval_cache[(pred, local_state)]

    def add_local_state(self, s: State) -> int:
        self._states.append(s)
        self._states_pickled_cache.append(pickle.dumps(s, pickle.HIGHEST_PROTOCOL))
        return len(self._states) - 1

    async def IG2_worker(self, conn: AsyncConnection) -> None:
        sys.stdout = self._logs._sep_log
        print("Started Worker")
        prog = syntax.the_program
        sep = FixedImplicationSeparatorPyCryptoSat(self._sig, (), PrefixConstraints(), 0, set(), [])
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
                prefix = v['prefix']
                del sep
                sep = FixedImplicationSeparatorPyCryptoSat(self._sig, prefix, k_cubes = 2, expt_flags = utils.args.expt_flags)
                sep_constraints = set()
                sep_constraints_order = []
                mapping = {}
                sep_time, eval_time = 0.0, 0.0
            if 'constraints' in v:
                (cons, extra_states) = v['constraints']
                states.update((i, pickle.loads(p)) for i,p in extra_states.items())
                constraints = list(cons)
            if 'block_last_separator' in v:
                sep.block_last_separator()
            if 'sep' in v:
                minimized = False
                while True:
                    print(f"Separating with prefix {prefix}")
                    start = time.time()
                    sep_r = sep.separate(minimize=minimized)
                    sep_time += time.time() - start
                    if sep_r is None:
                        print(f"UNSEP |core|={len(sep_constraints)} in (sep {sep_time:0.3f}, eval {eval_time:0.3f})")
                        await conn.send({'unsep': True, 'constraints': sep_constraints_order})
                        break

                    with prog.scope.n_states(1):
                        p = formula_to_predicate(sep_r, prog.scope)
                    print(f"Internal candidate: {p}")
                    start = time.time()
                    for c in constraints:
                        if c in sep_constraints: continue
                        if not satisifies_constraint(c, p, states):
                            print(f"Adding internal constraint {c}")
                            for s in c.states():
                                if s not in mapping:
                                    mapping[s] = sep.add_model(state_to_model(states[s]))
                            sep.add_constraint(c.map(mapping))
                            sep_constraints.add(c)
                            sep_constraints_order.append(c)
                            minimized = False
                            eval_time += time.time() - start
                            break
                    else:
                        eval_time += time.time() - start
                        # All known constraints are satisfied
                        if not minimized:
                            minimized = True
                            continue # continue the loop, now asking for a minimized separator
                        else:
                            print(f"Satisfied with {p} in (sep {sep_time:0.3f}, eval {eval_time:0.3f})")
                            await conn.send({'candidate': p, 'constraints': sep_constraints_order})
                            break

    async def check_candidate(self, p: Expr) -> Union[Constraint, z3.CheckSatResult]:
        minimize = 'no-minimize-cex' not in utils.args.expt_flags
        # F_0 => p?
        initial_state = await robust_check_implication([init.expr for init in syntax.the_program.inits()], p, minimize=minimize, parallelism=2, timeout=500, log=self._logs._smt_log)
        if isinstance(initial_state, Trace):
            self._print("Adding initial state")
            return Pos(self.add_local_state(initial_state.as_state(0)))
        elif initial_state == z3.unknown:
            self._print("Warning, implication query returned unknown")
                
        # F_i-1 ^ p => wp(p)?
        edge = await robust_check_transition([p, *self._frame], p, minimize=minimize, parallelism=2, timeout=500, log=self._logs._smt_log)

        if isinstance(edge, Trace):
            self._print(f"Adding edge")
            return Imp(self.add_local_state(edge.as_state(0)), self.add_local_state(edge.as_state(1)))
        return z3.unsat if edge == z3.unsat and edge == z3.unsat else z3.unknown


    def prefix_generators(self, pc: PrefixConstraints) -> Iterator[Iterator[Prefix]]:
        alts = 0 if pc.logic == Logic.Universal else pc.max_alt + 1
        for d in range(10):
            for alt in [0] if alts == 0 else range(1, min(d, alts)):
                if (d, alt) not in self._prefix_generators:
                    # print(f"Starting {d} {alt}")
                    self._prefix_generators[(d, alt)] = generate_exclusive(len(self._sig.sorts), d, alt, self._max_repeats, alt > 0)
                yield self._prefix_generators[(d, alt)]
  
    def satisfies_epr(self, pc: PrefixConstraints, p: Prefix) -> bool:
        if pc.logic != Logic.EPR: return True
        for q_a, q_b in itertools.combinations(p.linearize(), 2):
            if q_a[0] != q_b[0] and (q_a[1], q_b[1]) in pc.disallowed_quantifier_edges:
                # print(f"Failed {q_a} {q_b}")
                return False
        return True

    def add_to_frame(self, f: Expr) -> None:
        self._frame.append(f)
        # TODO: invalidate all -> constraints that don't have pre-states satisfying f, and rework those predicates that are no longer unsep
    async def solve(self, n_threads: int = 1) -> Optional[Expr]:
        _log_ig_problem(self._log_prefix, self._rationale, Neg(0), list(self._reachable_constraints), self._states, self._frame, [inv for inv in syntax.the_program.invs()])

        solution: asyncio.Future[Optional[Expr]] = asyncio.Future()

        if utils.args.logic == 'universal':
            pcs = [PrefixConstraints(Logic.Universal)]
        elif utils.args.logic == 'epr':
            pcs = [PrefixConstraints(Logic.Universal),
                   PrefixConstraints(Logic.Universal),
                   PrefixConstraints(Logic.EPR, max_alt=1),
                   PrefixConstraints(Logic.EPR, max_alt=1),
                   PrefixConstraints(Logic.EPR, max_alt=2)]
        elif utils.args.logic == 'fol':
            pcs = [PrefixConstraints(Logic.Universal),
                   PrefixConstraints(Logic.Universal),
                   PrefixConstraints(Logic.FOL, max_alt=1),
                   PrefixConstraints(Logic.FOL, max_alt=1),
                   PrefixConstraints(Logic.FOL, max_alt=2)]
        else:
            assert False
        for _pc in pcs:
            if _pc.logic == Logic.EPR:
                qe = [(self._sig.sort_indices[x], self._sig.sort_indices[y])
                      for (x,y) in itertools.product(self._sig.sort_names, self._sig.sort_names)
                      if (x,y) not in utils.args.epr_edges]
                _pc.disallowed_quantifier_edges = qe
        
        pcs_stopped = [False] * len(pcs)
        pcs_worked_on = [0] * len(pcs)
        def get_prefix() -> Optional[Tuple[Prefix, Callable[[], None]]]:
            possiblities = [(i, count) for (i, count) in enumerate(pcs_worked_on) if not pcs_stopped[i]]
            random.shuffle(possiblities) # fairly divide up effort when there are more threads than pcs
            if len(possiblities) == 0: raise StopIteration
            pc_index, _ = min(possiblities, key = lambda x: x[1])
            pcs_worked_on[pc_index] += 1
            pc = pcs[pc_index]
            def release() -> None:
                nonlocal pcs_worked_on
                pcs_worked_on[pc_index] -= 1
            
            try:
                while True:
                    candidate = next(itertools.chain.from_iterable(self.prefix_generators(pc)))
                    if not self.satisfies_epr(pc, candidate):
                        self._print("Skipping", " ".join(('A' if fa == True else 'E' if fa == False else 'Q') + self._sig.sort_names[sort_i] + '.' for (fa, sort_i) in candidate.linearize()))
                        continue
                    return (candidate, release)
            except StopIteration:
                pcs_stopped[pc_index] = True
                return None
                
            

        async def worker_controller() -> None:
            worker_known_states: Set[int] = set()
            worker_prefix_sent = False
                    
            def send_constraints(cs: List[Constraint]) -> Tuple[List[Constraint], Dict[int, bytes]]:
                new_states = set(s for c in cs for s in c.states()).difference(worker_known_states)
                extra_states = {i: self._states_pickled_cache[i] for i in new_states}
                worker_known_states.update(new_states)
                return (cs, extra_states)

            def predict_useful_constraints(prefix: Prefix) -> List[Constraint]:
                cores:List[List[Optional[Constraint]]] = []
                for sub_p in subprefixes(prefix):
                    if sub_p in self._unsep_cores:
                        sub_core: List[Optional[Constraint]] = list(reversed(self._unsep_cores[sub_p]))
                        sub_core.sort(key = lambda x: not isinstance(x, Pos))
                        cores.append(sub_core)
                #print(f"cores: {cores}")
                cores.append([None, None, None, *(x for x in self._reachable_constraints)])
                random.shuffle(cores)

                return [x for x in itertools.chain.from_iterable(itertools.zip_longest(*cores)) if x is not None]


            with ScopedProcess(self.IG2_worker) as conn:
                # Loop over prefixes
                while True:
                    # get a prefix.
                    try:
                        prefix_release = get_prefix()
                    except StopIteration:
                        self._print("Stopping worker")
                        return
                    if prefix_release is None:
                        continue
                    prefix, release = prefix_release
                    pre_pp = " ".join(('A' if fa == True else 'E' if fa == False else 'Q') + self._sig.sort_names[sort_i] + '.' for (fa, sort_i) in prefix.linearize())
                                        
                    # start a separator instance
                    worker_prefix_sent = False
                    next_constraints = list(self._necessary_constraints) + predict_useful_constraints(prefix)

                    start_time = time.time()
                    logged_problem = False
                    log_name = f"ig-{self._identity}-{self._sep_problem_index}"
                    self._sep_problem_index += 1
                    self._print(f"Trying: {pre_pp}")
                    # Loop for adding constraints for a particular prefix
                    while True:
                        await conn.send({'constraints': send_constraints(next_constraints), 'sep': None,
                                         **({'prefix': prefix.linearize()} if not worker_prefix_sent else {})})
                        worker_prefix_sent = True
                        if not logged_problem and time.time() - start_time > 5:
                            _log_sep_problem(log_name, prefix.linearize(), next_constraints, self._states, self._frame)
                            logged_problem = True

                        v = await conn.recv()
                        if 'candidate' in v:
                            p, sep_constraints = cast(Expr, v['candidate']), cast(List[Constraint], v['constraints'])
                            self._unsep_cores[prefix] = sep_constraints # share our constraints with others that may be running
                            new_constraint_result = await self.check_candidate(p)
                            if new_constraint_result == z3.unknown:
                                self._print(f"Solver returned unknown ({p})")
                                await conn.send({'block_last_separator': None})
                                continue
                            if isinstance(new_constraint_result, Constraint):
                                next_constraints = [new_constraint_result, *self._necessary_constraints, *predict_useful_constraints(prefix)]
                                self._total_constraints_found += 1
                                continue
                            elif new_constraint_result == z3.unsat:
                                if not solution.done():
                                    # if utils.args.log_dir != '':
                                    #     states_needed = set(s for c in sep_constraints for s in c.states())
                                    #     structs = dict((i, s) for i, s in enumerate(self._states) if i in states_needed)
                                    #     with open(os.path.join(utils.args.log_dir, f'ig-solutions/ig-solution-{self._log_prefix}.pickle'), 'wb') as output:
                                    #         pickle.dump({'states': structs, 'constraints': sep_constraints, 'solution': p, 'prior_frame': self._frame}, output)
                                    self._print(f"SEP with |constr|={len(sep_constraints)}")
                                    self._print(f"Learned {p}")
                                    solution.set_result(p)
                                return
                            assert False

                        elif 'unsep' in v:
                            core: List[Constraint] = v['constraints']
                            t = time.time() - start_time
                            if t > 5:
                                _log_sep_unsep('core-'+log_name, prefix.linearize(), core, self._states)
                                self._print(f"UNSEP: {pre_pp} with core={len(core)} time {t:0.3f} log core-{log_name}")
                            else:
                                self._print(f"UNSEP: {pre_pp} with core={len(core)} time {t:0.3f}")

                            self._unsep_cores[prefix] = core
                            release()
                            break
                        else:
                            assert False

        async def logger() -> None:
            query_start = time.time()
            while True:
                try: await asyncio.sleep(30)
                except asyncio.CancelledError:
                    self._print(f"finished in: {time.time() - query_start:0.3f} sec",
                                f"constraints:{self._total_constraints_found}",
                                f"({'cancelled' if solution.cancelled() else 'done'})")
                    raise
                self._print(f"time: {time.time() - query_start:0.3f} sec constraints:{self._total_constraints_found}")

        async with ScopedTasks() as tasks:
            tasks.add(logger())
            tasks.add(*(worker_controller() for _ in range(n_threads)))
            s = await solution
            self._print("Exiting IG_manager")
            return s


class ParallelFolIc3:
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
        self._threads_per_ig = 1
        
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
        self._logs = Logging(utils.args.log_dir)
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
        print(f"time: {time.time() - self._start_time:0.3f} sec")

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
            cex = await robust_check_transition(list(self._predicates[j] for j in fp), p, minimize='no-minimize-block' not in utils.args.expt_flags, parallelism=10, log=self._logs._smt_log)
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
            print(f"Pushing completed in {time.time() - start:0.3f} sec")

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

    async def parallel_inductive_generalize(self, frame: int, state: int, rationale: str = '') -> None:
        ig_frame = set(self.frame_predicates(frame-1))
        ig_generalizer = IGSolver2(self._states[state],
                                  [self._states[x] for x in self._useful_reachable | self._initial_states],
                                  [self._predicates[x] for x in ig_frame],
                                  self._logs, syntax.the_program, rationale, self._next_ig_query_index)
        self._next_ig_query_index += 1
        # TODO: 
        # cancel due to timeout
        
        sol: asyncio.Future[Optional[Expr]] = asyncio.Future()
        async with ScopedTasks() as tasks:
            async def frame_updater()-> None:
                while True:
                    current_frame = set(self.frame_predicates(frame-1))
                    if ig_frame != current_frame:
                        for f in current_frame - ig_frame:
                            ig_generalizer.add_to_frame(self._predicates[f])
                    await self._event_frames.wait()

            async def concurrent_block()-> None:
                while True:
                    if any(not self.eval(pred, state) for pred in self.frame_predicates(frame)):
                        print(f"State {state} was blocked in frame {frame} by concurrent task")
                        if not sol.done():
                            sol.set_result(None)
                        else:
                            break
                    await self._event_frames.wait()

            async def solver() -> None:
                x = await ig_generalizer.solve(self._threads_per_ig)
                if not sol.done():
                    sol.set_result(x)
            
            tasks.add(frame_updater())
            tasks.add(concurrent_block())
            tasks.add(solver())
            p = await sol

        if p is None or any(not self.eval(pred, state) for pred in self.frame_predicates(frame)):
            print(f"IG query cancelled ({state} in frame {frame} for {rationale})")
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
            edge = await robust_check_transition([self._predicates[i] for i in fp], formula_to_block, minimize='no-minimize-block' not in utils.args.expt_flags, parallelism=2, log=self._logs._smt_log)
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
                if index not in self._bad_predicates and not st.eval(p):
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
        if pred in self._safeties or pred in self._bad_predicates:
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
        thread_budget = utils.args.cpus if utils.args.cpus is not None else 10
        self._threads_per_ig = max(1, thread_budget//2) if 'no-heuristic-pushing' not in utils.args.expt_flags else thread_budget
        async with ScopedTasks() as tasks:
            if 'no-heuristic-pushing' not in utils.args.expt_flags:
                tasks.add(self.heuristic_pushing_to_the_top_worker(True))
                # tasks.add(self.heuristic_pushing_to_the_top_worker(True))
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
    old_stdout = sys.stdout
    if utils.args.log_dir:
        os.makedirs(utils.args.log_dir, exist_ok=True)
        for dir in ['smt-queries', 'ig-problems', 'sep-unsep', 'sep-problems']:
            os.makedirs(os.path.join(utils.args.log_dir, dir), exist_ok=True)
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
    # Check EPR-ness
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
    print('epr_edges =',repr(','.join(f'{a}->{b}' for a,b in edges)))
    g = networkx.DiGraph()
    g.add_edges_from(edges)
    print(f"graph is acyclic: {networkx.is_directed_acyclic_graph(g)}")

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

def _incremental_unsat(s: z3.Solver, assertions: List[z3.ExprRef]) -> z3.CheckSatResult:
    s.push()
    try:
        s.set('timeout', 3000)
        s.set('seed', random.randint(0, 1000000000))
        while True:
            r = s.check()
            if r == z3.unsat:
                print("unsat")
                return z3.unsat
            if r == z3.unknown:
                print("unknown")
                return z3.unknown
            if r == z3.sat:
                print("sat")
                m = s.model()
                random.shuffle(assertions)
                for i, a in enumerate(assertions):
                    if not z3.is_true(m.eval(a, model_completion=True)):
                        print(f"adding {a}")
                        s.add(a)
                        assertions = assertions[:i]+assertions[i+1:]
                        break
                else:
                    print("sat")
                    return z3.sat
    finally:
        s.pop()

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
            print(f"{expr}")
    
    else:
        assert False

def fol_benchmark_solver(_: Solver) -> None:
    if utils.args.output:
        sys.stdout = open(utils.args.output, "w")
    print(f"Benchmarking {utils.args.query} ({utils.args.filename})")
    data = pickle.load(open(utils.args.query, 'rb'))
    if len(data) == 4:
        (old_hyps, new_conc, minimize, transition_name) = cast(Tuple[List[Expr], Expr, Optional[bool], Optional[str]], data)
        states = 2
    else:
        (old_hyps, new_conc, minimize) = cast(Tuple[List[Expr], Expr, Optional[bool]], data)
        states = 1
    if True:
        print('Analyzing')
        for e in old_hyps:
            print("  ", e)
        print("  ", new_conc)
        def make_formula(s: Solver, t: Z3Translator, prog_scope: Scope, transition: DefinitionDecl) -> None:
            if states == 2:
                for e in [New(Not(new_conc)), transition.as_twostate_formula(prog_scope)]:
                    s.add(t.translate_expr(e))
            else:
                s.add(t.translate_expr(Not(new_conc)))
            exprs = list(old_hyps)
            # random.shuffle(exprs)
            for e in exprs:
                s.add(t.translate_expr(e))
            
        formulas = [(lambda s, t, trans=transition: make_formula(s, t, syntax.the_program.scope, trans)) for transition in syntax.the_program.transitions()]
        s = Solver()
        t = s.get_translator(2)
        for f_i, (f, transition) in enumerate(zip(formulas, syntax.the_program.transitions())):
            #with open(f"{f_i}-{transition.name}.smt2", "w") as out:
                with s.new_frame():
                    f(s, t)
                    # Write out to .smt2 files
                    #out.write('(set-logic UF)\n')
                    #out.write(s.z3solver.to_smt2())

                    # Check EPR-ness
                    edges: Set[Tuple[str, str]] = set()
                    for func in syntax.the_program.functions():
                        for s1 in func.arity:
                            edges.add((str(s1), str(func.sort)))
                    for a in s.z3solver.assertions():
                        add_epr_edges(edges, a)
                    print(edges)
                    g = networkx.DiGraph()
                    g.add_edges_from(edges)
                    print(f"graph is acyclic: {networkx.is_directed_acyclic_graph(g)}")
                    assertions = list(s.z3solver.assertions())
                if f_i == 2:
                    while True:
                        ss = Solver()
                        r = _incremental_unsat(ss.z3solver, assertions)
                        print(f"Result: {r}")
                        if r != z3.unknown:
                            break
    
    if False:
        start = time.time()
        r = asyncio.run(robust_check_transition(old_hyps, new_conc, parallelism=10, timeout=0))
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
    if False:
        tr = next(t for t in syntax.the_program.transitions() if t.name == 'receive_join_acks')

        _find_unsat_core(tr, old_hyps, new_conc)
        print("Original timings")
        print("With z3:")
        _check_core_unsat_times(tr, old_hyps, new_conc, False)
        print("With cvc4:")
        _check_core_unsat_times(tr, old_hyps, new_conc, True)
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


def fol_benchmark_ig(_: Solver) -> None:
    tp = Tuple[str, Neg, List[Constraint], Dict[int, State], List[Expr], List[InvariantDecl]]
    (rationale, block, pos, states, prior_frame, golden) = cast(tp, pickle.load(open(utils.args.query, 'rb')))
    print(f"IG query for {rationale}")
    async def run_query() -> None:
        logs = Logging('')
        logs._smt_log = open('/dev/null', 'w')
        logs._sep_log = open('/dev/null', 'w')
        if 'ig2' in utils.args.expt_flags:
            ig2 = IGSolver2(states[block.i],
                            [states[x.i] for x in pos if isinstance(x, Pos)],
                            prior_frame,
                            logs, syntax.the_program, rationale, 0)
            await ig2.solve(10)
        else:
            ig = IGSolver(states[block.i],
                          [states[x.i] for x in pos if isinstance(x, Pos)],
                          prior_frame,
                          logs, syntax.the_program, rationale, 0)
            await ig.solve(10)
        
        
    asyncio.run(run_query())
    
def fol_benchmark_sep_unsep(_: Solver) -> None:
    (prefix, constraints, states) = cast(Tuple[Tuple[Tuple[Optional[bool], int], ...], List[Constraint], Dict[int, State]], pickle.load(open(utils.args.query, 'rb')))
    print(f"Prefix is: {prefix}, len(constraints) = {len(constraints)}")
    sig = prog_to_sig(syntax.the_program, two_state=False)
    sep = FixedImplicationSeparatorPyCryptoSat(sig, prefix, PrefixConstraints())
    mapping = {}
    start = time.time()
    cand: Optional[separators.logic.Formula] = None
    for c in constraints:
        for s in c.states():
            if s not in mapping:
                mapping[s] = sep.add_model(state_to_model(states[s]))
        sep.add_constraint(c.map(mapping))
        cand = sep.separate()
        print(f"Candidate: {cand}")
    if cand is not None:
        print("Warning, expected UNSEP not {cand}")
    end = time.time()
    print(f"Elapsed: {end-start:0.3f}")

def decompose_prenex(p: Expr) -> Tuple[List[Tuple[bool, str, str]], Expr]:
    def binder_to_list(b: syntax.Binder, is_forall: bool) -> List[Tuple[bool, str, str]]:
        return [(is_forall, v.name, cast(UninterpretedSort, v.sort).name) for v in b.vs]
    if isinstance(p, QuantifierExpr):
        sub_prefix, matrix = decompose_prenex(p.body)
        return (binder_to_list(p.binder, p.quant == 'FORALL') + sub_prefix, matrix)
    else:
        return ([], p)

def compose_prenex(prefix: Sequence[Tuple[bool, str, str]], matrix: Expr) -> Expr:
    def _int(prefix: Sequence[Tuple[bool, str, str]], matrix: Expr) -> Expr:
        if len(prefix) == 0: return matrix
        sub_formula = _int(prefix[1:], matrix)
        (is_forall, var, sort) = prefix[0]
        if is_forall:
            v = SortedVar(var, UninterpretedSort(sort))
            if isinstance(sub_formula, QuantifierExpr) and sub_formula.quant == 'FORALL':
                return Forall((v, *sub_formula.binder.vs), sub_formula.body)
            return Forall((v,), sub_formula)
        else:
            v = SortedVar(var, UninterpretedSort(sort))
            if isinstance(sub_formula, QuantifierExpr) and sub_formula.quant == 'EXISTS':
                return Exists((v, *sub_formula.binder.vs), sub_formula.body)
            return Exists((v,), sub_formula)
    e = _int(prefix, matrix)
    with syntax.the_program.scope.n_states(2):
        typecheck_expr(syntax.the_program.scope, e, BoolSort)
    return e

def generalizations_of_prefix(prefix: List[Tuple[bool, str, str]]) -> Iterable[List[Tuple[bool, str, str]]]:
    alternations = [list(g) for (_, g) in itertools.groupby(prefix, key = lambda x: x[0])]

    # Turn an entire block of Exists into forall at once.
    # for i, quantifier_block in enumerate(alternations):
    #     if quantifier_block[0][0]: continue
    #     yield list(itertools.chain.from_iterable(alternations[:i] + [[(True, v, s) for (_, v, s) in alternations[i]]] + alternations[i+1:]))

    # Turn each E into a A individually, and lift it to the top of its block of E.
    # So if we pick x in AAAEExEA, the resulting quantifier is AAAAxEEA
    for i, (is_forall, var, sort) in enumerate(prefix):
        if is_forall: continue
        j = i
        while j > 0 and not prefix[j-1][0]:
            j -= 1
        without_i = prefix[:i] + prefix[i+1:]
        yield without_i[:j] + [(True, var, sort)] + without_i[j:]

    # Swap EA into AE, a whole quantifier block at a time. AAA(EEEAA) becomes AAA(AAEEE).
    # Guaranteed to not introduce more alternations
    for i, quantifier_block in enumerate(alternations):
        if quantifier_block[0][0]: continue
        if i + 1 == len(alternations): continue
        yield list(itertools.chain.from_iterable(alternations[:i] + [alternations[i+1], alternations[i]] + alternations[i+2:]))

def prefix_in_epr(prefix: List[Tuple[bool, str, str]]) -> bool:
    for q_a, q_b in itertools.combinations(prefix, 2):
        if q_a[0] != q_b[0] and (q_a[2], q_b[2]) not in utils.args.epr_edges:
            # print(f"Failed {q_a} {q_b}")
            return False
    return True


async def check_candidate(p: Expr, prior_frame: List[Expr]) -> bool:
    # F_0 => p?
    initial_state = await robust_check_implication([init.expr for init in syntax.the_program.inits()], p, log=open("/dev/null", 'w'))
    if initial_state is not None:
        return False

    # F_i-1 ^ p => wp(p)?
    edge = await robust_check_transition([p, *prior_frame], p, parallelism = 2, timeout=500, log=open("/dev/null", 'w'))
    if edge == z3.unsat:
        return True
    return False

def generalize_quantifiers(p: Expr, constraints: Set[Constraint], states: Dict[int, State], prior_frame: List[Expr]) -> Expr:
    prefix, matrix = decompose_prenex(p)
    print(f"Original prefix {prefix}, matrix {matrix}")
    assert prefix_in_epr(prefix)
    while True:
        for new_prefix in generalizations_of_prefix(prefix):
            assert new_prefix != prefix
            if not prefix_in_epr(new_prefix) and 'generalize-non-epr' not in utils.args.expt_flags:
                print(f"Not in EPR")
                continue
            q = compose_prenex(new_prefix, matrix)
            print(f"Trying... {q}")
            if all(satisifies_constraint(c, q, states) for c in constraints):
                print("Passed constraints")
                if asyncio.run(check_candidate(q, prior_frame)):
                    print("Accepted new formula")
                    prefix = new_prefix
                    break
                print("Not relatively inductive")
            else:
                print("Rejected by constraints")
        else:
            break
    return compose_prenex(prefix, matrix)

def fol_debug_ig(_: Solver) -> None:
    # if utils.args.output:
    #     sys.stdout = open(utils.args.output, "w")
    print(f"Benchmarking {utils.args.query} ({utils.args.filename})")
    data = pickle.load(open(utils.args.query, 'rb'))
    p: Expr = data['solution']
    constraints: List[Constraint] = data['constraints']
    states: Dict[int, State] = data['states']
    prior_frame: List[Expr] = data['prior_frame']
    print(f"Initial solution: {p}")
    # for q in prior_frame:
    #     print(q)
    pp = generalize_quantifiers(p, set(constraints), states, prior_frame)
    if pp != p:
        print(f"(GEN) Generalized to: {pp}")
        print(f"(GEN) From:           {p}")
    else:
        print("Could not generalize")
    
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
    s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: set(x.split(',')), default=set(), help="Experimental flags")
    s.add_argument("--log-dir", dest="log_dir", type=str, default="", help="Log directory")
    s.add_argument("--cpus", dest="cpus", type=int, default=10, help="CPU threads to use (best effort only)")
    result.append(s)

    s = subparsers.add_parser('fol-extract', help='Extract conjuncts to a file')
    s.set_defaults(main=fol_extract)
    s.add_argument("--logic", choices=('fol', 'epr', 'universal'), default="fol", help="Restrict form of separators to given logic (fol is unrestricted)")
    s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: set(x.split(',')), default=set(), help="Experimental flags")
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
    s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: set(x.split(',')), default=set(), help="Experimental flags")
    result.append(s)

    s = subparsers.add_parser('fol-benchmark-ig', help='Test IG query solver')
    s.set_defaults(main=fol_benchmark_ig)
    s.add_argument("--query", type=str, help="Query to benchmark")
    s.add_argument("--output", type=str, help="Output to file")
    s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: set(x.split(',')), default=set(), help="Experimental flags")
    s.add_argument("--log-dir", dest="log_dir", type=str, default="", help="Log directory")
    s.add_argument("--logic", choices=('fol', 'epr', 'universal'), default="fol", help="Restrict form of separators to given logic (fol is unrestricted)")
    s.add_argument("--epr-edges", dest="epr_edges", type=epr_edges, default=[], help="Allowed EPR edges in inferred formula")
    result.append(s)

    s = subparsers.add_parser('fol-benchmark-sep-unsep', help='Test IG query solver')
    s.set_defaults(main=fol_benchmark_sep_unsep)
    s.add_argument("--query", type=str, help="Query to benchmark")
    s.add_argument("--output", type=str, help="Output to file")
    s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: set(x.split(',')), default=set(), help="Experimental flags")
    result.append(s)

    # s = subparsers.add_parser('fol-benchmark-ig', help='Test IG query solver')
    # s.set_defaults(main=fol_benchmark_ig)
    # s.add_argument("--query", type=str, help="Query to benchmark")
    # s.add_argument("--output", type=str, help="Output to file")
    # s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: set(x.split(',')), default=set(), help="Experimental flags")
    # result.append(s)

    s = subparsers.add_parser('fol-debug-ig', help='Debug a IG solution')
    s.set_defaults(main=fol_debug_ig)
    s.add_argument("--query", type=str, help="Solution to query")
    s.add_argument("--epr-edges", dest="epr_edges", type=epr_edges, default=[], help="Allowed EPR edges in inferred formula")
    s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: set(x.split(',')), default=set(), help="Experimental flags")
    # s.add_argument("--output", type=str, help="Output to file")
    result.append(s)

    return result
