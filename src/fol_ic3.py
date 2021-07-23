
from typing import Any, Callable, DefaultDict, Dict, Iterable, Iterator, Sequence, TextIO, List, Optional, Set, Tuple, Union, cast

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

from async_tools import AsyncConnection, FileDescriptor, ScopedProcess, ScopedTasks, ForkServer
from semantics import State
from separators.logic import Signature
import utils
from logic import Diagram, Expr, Solver, Trace
import syntax
from syntax import BinaryExpr, DefinitionDecl, IfThenElse, InvariantDecl, Let, NaryExpr, New, Not, Program, QuantifierExpr, TrueExpr, UnaryExpr
from fol_trans import eval_predicate, formula_to_predicate, predicate_to_formula, prog_to_sig, state_to_model
from separators import Constraint, Neg, Pos, Imp
from separators.separate import FixedImplicationSeparatorPyCryptoSat, Logic, PrefixConstraints

import networkx
import z3
from solver_cvc5 import CVC5Solver, SatResult

_forkserver = cast(ForkServer, None) # This needs to be initialized in 'main', before launching threads/asyncio but after globals (syntax.the_program, etc.) are filled in.

# This is a class designed to cache the result of pickling.
# This helps the main process which needs to serialize lemmas many times in robust_check_implication
# It deserializes directly into the underlying Expr. This caching relies on Exprs being immutable.
# class TopLevelExpr:
#     def __init__(self, v: Expr):
#         self.v = v
#         self.cache: Optional[bytes] = None
#     def reduce(self) -> Tuple[Any, Tuple]:
#         if self.cache is None:
#             self.cache = pickle.dumps(self.v)
#         return pickle.loads, (self.cache,)
# copyreg.pickle(TopLevelExpr, cast(Any, TopLevelExpr.reduce))

_robust_id = 0
def _get_robust_id() -> str:
    global _robust_id
    id = f'{_robust_id:06d}'
    _robust_id += 1
    return id

@dataclass
class RobustCheckResult:
    result: SatResult
    trace: Optional[Trace] = None
    # core: Set[Expr] = field(default_factory = set)
    # transition: Optional[str] = None
    # time: float = 0.0
    @staticmethod
    def from_z3_or_trace(r: Union[z3.CheckSatResult, Trace]) -> 'RobustCheckResult':
        if isinstance(r, Trace):
            return RobustCheckResult(SatResult.sat, r)
        elif r == z3.unsat:
            return RobustCheckResult(SatResult.unsat, None)
        else:
            return RobustCheckResult(SatResult.unknown, None)

class RobustChecker:
    async def check_implication(self, hyps: Iterable[Expr], conc: Expr, parallelism: int = 1, timeout: float = 0.0) -> RobustCheckResult: ...
    async def check_transition(self, hyps: Iterable[Expr], conc: Expr, parallelism: int = 1, timeout: float = 0.0) -> RobustCheckResult: ...
    

def _fancy_check_transition2_internal(hyps: List[Expr], new_conc: Expr, tr: Expr, timeout: float = 1.0, _print: Callable = print) -> Union[List[int], None, Trace]:
    sat_inst = z3.Optimize()
    for i in range(len(hyps)):
        sat_inst.add_soft(z3.Not(z3.Bool(f'I_{i}')))
    # sat_inst.add(z3.Bool('I_0'))
    order: List[int] = []
    badness = [0 for _ in range(len(hyps))]
    unknown_count = 0
    while True:
        solver = CVC5Solver(syntax.the_program, timeout = int(timeout * 1000))
        with solver.new_scope(2):
            solver.add_expr(tr)
            solver.add_expr(New(Not(new_conc)))

            while True:
                # result = sat_inst.check(*(z3.Not(z3.Bool(f'I_{i}')) for i in order))
                result = sat_inst.check()
                if result == z3.sat:
                    sel2 = []
                    m = sat_inst.model()
                    sel2 = [z3.is_true(m.eval(z3.Bool(f'I_{i}'), model_completion=True)) for i in range(len(hyps))]
                    del m
                    break
                else:
                    return None
                    if len(order) == 0:
                        assert False
                    order.pop()
            
            # _print(''.join(str(i) if i < 10 else '+' for i in badness), "badness")
            # while True:
            #     result = sat_inst.check(*(z3.Not(z3.Bool(f'I_{i}')) for i in order))
            #     if result == z3.sat:
            #         m = sat_inst.model()
            #         sel2 = [z3.is_true(m.eval(z3.Bool(f'I_{i}'), model_completion=True)) for i in range(len(hyps))]
            #         del m
            #         break
            #     else:
            #         order.pop() # should be safe as we only add positive literal clauses
            
            for hyp, selected in zip(hyps, sel2):
                if selected:
                    solver.add_expr(hyp)
            to_add = -1

            while True:
                r = solver.check()
                _print(''.join('1' if v else '.' for v in sel2), r)
    
                if r == SatResult.unsat:
                    return [i for i in range(len(hyps)) if sel2[i]]
                elif r == SatResult.unknown:
                    # order = [i for i in range(len(hyps)) if sel2[i]]
                    # random.shuffle(order)
                    cl = []
                    for i in range(len(hyps)):
                        if sel2[i]:
                            cl.append(z3.Not(z3.Bool(f'I_{i}')))
                    sat_inst.add(z3.Or(*cl))
                    
                    if to_add != -1:
                        badness[to_add] += 1
                    else:
                        pass
                        # for i in range(len(hyps)):
                        #     if sel2[i]:
                        #         badness[i] += 1
                    unknown_count += 1
                    break
                elif r == SatResult.sat:
                    trace = solver.get_trace()
                    pre_state = trace.as_state(0)
                    disprovers = [not pre_state.eval(hyps[i]) for i in range(len(hyps))]
                    _print(''.join('-' if v else '.' for v in disprovers), '   model', sum(1 if v else 0 for v in disprovers))

                    for i, dis, ssss in zip(range(len(hyps)), disprovers, sel2):
                        if dis and ssss:
                            assert False, hyps[i]
                    # _print([solver.is_true(hyps[i]) for i in range(len(hyps))])
                    # disprovers = [not(solver.is_true(hyps[i])) for i in range(len(hyps))]
                    
                    # _print("size of clause", sum([1 if v else 0 for i, v in enumerate(disprovers)]))
                    sat_inst.add(z3.Or([z3.Bool(f'I_{i}') for i, v in enumerate(disprovers) if v]))
                    if not any(disprovers):
                        return trace
                    to_add_possibilities = [i for i in range(len(hyps)) if disprovers[i]]
                    # random.shuffle(to_add_possibilities)
                    to_add_possibilities.sort(key = lambda i: badness[i])
                    to_add = to_add_possibilities[0]
                    # to_add = random.sample([i for i in range(len(hyps)) if disprovers[i]], 1)[0]
                    solver.add_expr(hyps[to_add])
                    sel2[to_add] = True
                    unknown_count = 0
                 
        del solver

async def _main_worker_advanced_transition(conn: AsyncConnection, stdout: FileDescriptor, log_prefix: str) -> None:
    sys.stdout = os.fdopen(stdout.id, 'w')
    sys.stdout.reconfigure(line_buffering=True)
    exprs: Dict[int, Expr] = {}
    tr: Expr = TrueExpr
    conc: Expr = TrueExpr
    def _print(*args: Any) -> None:
        print(log_prefix, *args)
    while True:
        v = await conn.recv()
        if 'exprs' in v:
            for id, e in v['exprs'].items():
                exprs[id] = e
        if 'formulas' in v:
            (tr, conc) = v['formulas']
        if 'solve' in v:
            (expr_ids, timeout) = v['solve']
            if v['solver'] == 'cvc5-fancy':
                r = _fancy_check_transition2_internal([exprs[i] for i in expr_ids], conc, tr, timeout=v['unk_timeout'], _print=_print)
                if isinstance(r, Trace):
                    await conn.send(RobustCheckResult(SatResult.sat, r))
                else:
                    await conn.send(RobustCheckResult(SatResult.unsat))
            elif v['solver'] == 'z3-basic' or v['solver'] == 'cvc4-basic':
                s = Solver(use_cvc4=v['solver'] == 'cvc4-basic')
                t = s.get_translator(2)
                with s.new_frame():
                    for i in expr_ids:
                        s.add(t.translate_expr(exprs[i]))
                    s.add(t.translate_expr(tr))
                    s.add(t.translate_expr(New(Not(conc))))
                    raw_result = s.check(timeout = min(1000000000, int(timeout * 1000)))
                    if raw_result == z3.unsat:
                        await conn.send(RobustCheckResult(SatResult.unsat))
                    else:
                        await conn.send(RobustCheckResult(SatResult.unknown))
                del t, s
            elif v['solver'] == 'cvc5-basic':
                s5 = CVC5Solver(syntax.the_program, int(timeout * 1000))
                with s5.new_scope(2):
                    for i in expr_ids:
                        s5.add_expr(exprs[i])
                    s5.add_expr(tr)
                    s5.add_expr(New(Not(conc)))
                    raw_result5 = s5.check()
                    if raw_result5 == SatResult.unsat:
                        await conn.send(RobustCheckResult(SatResult.unsat))
                    elif raw_result5 == SatResult.sat:
                        await conn.send(RobustCheckResult(SatResult.sat, s5.get_trace()))
                    else:
                        await conn.send(RobustCheckResult(SatResult.unknown, None))
                del s5

async def _main_worker_advanced_implication(conn: AsyncConnection, stdout: FileDescriptor, log_prefix: str) -> None:
    sys.stdout = os.fdopen(stdout.id, 'w')
    sys.stdout.reconfigure(line_buffering=True)
    exprs: Dict[int, Expr] = {}
    while True:
        v = await conn.recv()
        if 'exprs' in v:
            for id, e in v['exprs'].items():
                exprs[id] = e
        if 'solve' in v:
            (expr_ids, timeout) = v['solve']
            if v['solver'] == 'z3-basic' or v['solver'] == 'cvc4-basic':
                s = Solver(use_cvc4=v['solver'] == 'cvc4-basic')
                t = s.get_translator(1)
                with s.new_frame():
                    for i in expr_ids:
                        s.add(t.translate_expr(exprs[i]))
                    raw_result = s.check(timeout = min(1000000000, int(timeout * 1000)))
                    if raw_result == z3.unsat:
                        await conn.send(RobustCheckResult(SatResult.unsat))
                    else:
                        await conn.send(RobustCheckResult(SatResult.unknown))
                del t, s
            elif v['solver'] == 'cvc5-basic':
                s5 = CVC5Solver(syntax.the_program, int(timeout * 1000))
                with s5.new_scope(1):
                    for i in expr_ids:
                        s5.add_expr(exprs[i])
                    raw_result5 = s5.check()
                    if raw_result5 == SatResult.unsat:
                        await conn.send(RobustCheckResult(SatResult.unsat))
                    elif raw_result5 == SatResult.sat:
                        await conn.send(RobustCheckResult(SatResult.sat, s5.get_trace()))
                    else:
                        await conn.send(RobustCheckResult(SatResult.unknown, None))
                del s5

class AdvancedChecker(RobustChecker):
    def __init__(self, prog: Program, log: TextIO = sys.stdout) -> None:
        self._prog = prog
        self._log = log
        self._transitions: List[str] = [tr.name for tr in self._prog.transitions()]
        self._tr_formulas = {tr.name: tr.as_twostate_formula(self._prog.scope) for tr in self._prog.transitions()}
        self._last_successful: Dict[str, Tuple[str, float, float]] = {}
        self._log_id = _get_robust_id()
        self._query_id = 0

    def _get_log_prefix(self) -> str:
        prefix = f"[{self._log_id}-{self._query_id}]"
        self._query_id += 1
        return prefix
    def _print(self, prefix: str, *args: Any) -> None:
        print(prefix, *args, file=self._log)

    # Don't do anything special for implications
    async def check_implication(self, _hyps: Iterable[Expr], conc: Expr, parallelism: int = 1, timeout: float = 0.0) -> RobustCheckResult:
        log_prefix = self._get_log_prefix()
        formulas = [Not(conc), *_hyps]
        result: asyncio.Future[RobustCheckResult] = asyncio.Future()
        strategies = [ ('z3-basic', 0.25), ('cvc5-basic', 0.5), ('z3-basic', 2.0), ('cvc5-basic', 5.0), ('z3-basic', 10.0), ('cvc5-basic', 20.0)]
        def get_next_attempt() -> Iterable[Tuple[str, float]]:
            for attempt in range(1000000):
                yield strategies[min(len(strategies)-1, attempt)]
        strategy_gen = iter(get_next_attempt())
        
        async def worker() -> None:
            while not result.done():
                try: 
                    with ScopedProcess(_forkserver, _main_worker_advanced_implication, FileDescriptor(self._log.fileno()), log_prefix) as conn:
                        await conn.send({'exprs': {i: formulas[i] for i in range(len(formulas))}})
                        while not result.done():
                            (solver_type, timeout) = next(strategy_gen)
                            await conn.send({'solve': (list(range(len(formulas))), timeout), 'solver': solver_type})
                            resp: RobustCheckResult = await asyncio.wait_for(conn.recv(), timeout + 1)
                            if resp.result == SatResult.unsat:
                                if not result.done():
                                    result.set_result(RobustCheckResult(SatResult.unsat))
                            if resp.result == SatResult.sat:
                                if not result.done():
                                    result.set_result(resp)
                                
                except asyncio.TimeoutError:
                    self._print(log_prefix, "Resetting solver process")
                except StopIteration:
                    self._print(log_prefix, "Ran out of strategies")

        async def logger() -> None:
            await asyncio.sleep(5)
            if utils.args.log_dir != '':
                fname = f'query-im-{log_prefix}.pickle'
                with open(os.path.join(utils.args.log_dir, 'smt-queries', fname), 'wb') as f:
                    pickle.dump((list(formulas[1:]), conc), f, protocol=pickle.HIGHEST_PROTOCOL)

        try:
            async with ScopedTasks() as tasks:
                start = time.time()
                for i in range(parallelism):
                    tasks.add(worker())
                tasks.add(logger())
                rr = await asyncio.wait_for(result, timeout if timeout > 0 else None)
                self._print(log_prefix, f"Completed implication {rr.result} in {time.time() - start:0.3f}")
                return rr
        except asyncio.TimeoutError:
            self._print(log_prefix, "Implication query timed out")
            return RobustCheckResult(SatResult.unknown)

    async def check_transition(self, _hyps: Iterable[Expr], conc: Expr, parallelism: int = 1, timeout: float = 0.0) -> RobustCheckResult:
        log_prefix = self._get_log_prefix()
        hyps = list(_hyps)
        trs_unsat = {tr.name: False for tr in self._prog.transitions()}
        attempts_started = {tr.name: 0 for tr in self._prog.transitions()}
        result: asyncio.Future[RobustCheckResult] = asyncio.Future()
        #strategies = [('cvc5-basic', 0.5), ('z3-basic', 0.25), ('cvc5-fancy', 15.0), ('z3-basic', 5.0), ('cvc5-fancy', 30.0), ('z3-basic', 5.0), ('cvc5-fancy', 45.0)]
        #strategies = [('cvc5-fancy', 100000.0)]
        strategies = [('cvc5-basic', 0.5, 0), ('z3-basic', 0.25, 0), ('cvc5-fancy', 20.0, 2), ('cvc5-fancy', 400.0, 16), ('cvc5-fancy', 1600.0, 64)]
        
        def get_next_attempt() -> Iterable[Tuple[str, Tuple[str, float, float]]]:
            while True:
                for tr in self._transitions:
                    if not trs_unsat[tr]:
                        attempt_num = attempts_started[tr]
                        attempts_started[tr] += 1
                        if attempt_num == 0 and tr in self._last_successful:
                            st = self._last_successful[tr]
                        elif tr in self._last_successful:
                            st = strategies[min(len(strategies)-1, attempt_num-1)]
                        else:
                            st = strategies[min(len(strategies)-1, attempt_num)]
                        yield (tr, st)
        strategy_gen = iter(get_next_attempt())
        
 
        async def worker() -> None:
            while not result.done():
                try: 
                    with ScopedProcess(_forkserver, _main_worker_advanced_transition, FileDescriptor(self._log.fileno()), log_prefix) as conn:
                        await conn.send({'exprs': {i: hyps[i] for i in range(len(hyps))}})
                        while not result.done():
                            (tr, (solver_type, timeout, unk_timeout)) = next(strategy_gen)
                            await conn.send({'formulas': (self._tr_formulas[tr], conc), 'tr-name': tr, 'solve': (list(range(len(hyps))), timeout), 'solver': solver_type, 'unk_timeout': unk_timeout})
                            resp: RobustCheckResult = await asyncio.wait_for(conn.recv(), timeout + 1)
                            # Save the success solver type for this transition so it is tried first next time
                            if resp.result != SatResult.unknown:
                                self._last_successful[tr] = (solver_type, timeout, unk_timeout)
                            if resp.result == SatResult.unsat:
                                trs_unsat[tr] = True
                                if all(trs_unsat.values()) and not result.done():
                                    result.set_result(RobustCheckResult(SatResult.unsat))
                            if resp.result == SatResult.sat:
                                self._transitions = [tr, *(t for t in self._transitions if t != tr)]
                                if not result.done():
                                    result.set_result(resp)

                except asyncio.TimeoutError:
                    self._print(log_prefix, "Resetting solver process")
                except StopIteration:
                    self._print(log_prefix, "Ran out of strategies")

        async def logger() -> None:
            await asyncio.sleep(5)
            if utils.args.log_dir != '':
                fname = f'query-tr-{log_prefix}.pickle'
                with open(os.path.join(utils.args.log_dir, 'smt-queries', fname), 'wb') as f:
                    pickle.dump((hyps, conc), f, protocol=pickle.HIGHEST_PROTOCOL)

        try:
            async with ScopedTasks() as tasks:
                start = time.time()
                for i in range(parallelism):
                    tasks.add(worker())
                tasks.add(logger())
                rr = await asyncio.wait_for(result, timeout if timeout > 0 else None)
                self._print(log_prefix, f"Completed transition {rr.result} in {time.time() - start:0.3f}")
                return rr
        except asyncio.TimeoutError:
            self._print(log_prefix, "Transition query timed out")
            return RobustCheckResult(SatResult.unknown)

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

class Logging:
    def __init__(self, log_dir: str) -> None:
        self._log_dir = log_dir
        self._sep_log_fname = '/dev/null' if log_dir == '' else os.path.join(utils.args.log_dir, 'sep.log')
        self._sep_log: TextIO = open(self._sep_log_fname, 'w') if log_dir == '' else open(self._sep_log_fname, 'w', buffering=1)
        self._smt_log: TextIO = open('/dev/null', 'w') if log_dir == '' else open(os.path.join(utils.args.log_dir, 'smt.log'), 'w', buffering=1)
        self._ig_log: TextIO  = sys.stdout if log_dir == '' else open(os.path.join(utils.args.log_dir, 'ig.log'),  'w', buffering=1)


async def _main_IG2_worker(conn: AsyncConnection, sig: Signature, log_fname: str) -> None:
    sys.stdout = open(log_fname, "a")
    sys.stdout.reconfigure(line_buffering=True) # type: ignore
    print("Started Worker")
    prog = syntax.the_program
    sep = cast(FixedImplicationSeparatorPyCryptoSat, None)
    label = '[?]'
    sep_pc = PrefixConstraints()
    if utils.args.logic == 'epr':
        sep_pc.logic = Logic.EPR
        qe = [(sig.sort_indices[x], sig.sort_indices[y])
            for (x,y) in itertools.product(sig.sort_names, sig.sort_names)
            if (x,y) not in utils.args.epr_edges]
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
            sep = FixedImplicationSeparatorPyCryptoSat(sig, prefix, pc=sep_pc, k_cubes=k_cubes, expt_flags=expt_flags, debug=False)
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
            minimized_reset_value = 'always-minimize-sep' in utils.args.expt_flags
            minimized = minimized_reset_value
            while True:
                print(label, f"Separating with prefix {prefix}")
                start = time.time()
                sep_r = sep.separate(minimize=minimized)
                sep_time += time.time() - start
                if sep_r is None:
                    print(label, f"UNSEP |core|={len(sep_constraints)} in (sep {sep_time:0.3f}, eval {eval_time:0.3f})")
                    await conn.send({'unsep': True, 'constraints': sep_constraints_order, 'times': (sep_time, eval_time)})
                    break

                with prog.scope.n_states(1):
                    p = formula_to_predicate(sep_r, prog.scope)
                print(label, f"Internal candidate: {p}")
                start = time.time()
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
                        eval_time += time.time() - start
                        break
                    else:
                        evaled_constraints.append(c)
                else:
                    eval_time += time.time() - start
                    # All known constraints are satisfied
                    if not minimized:
                        minimized = True
                        continue # continue the loop, now asking for a minimized separator
                    else:
                        print(label, f"Satisfied with {p} in (sep {sep_time:0.3f}, eval {eval_time:0.3f})")
                        await conn.send({'candidate': p, 'constraints': sep_constraints_order, 'times': (sep_time, eval_time)})
                        break
                this_eval_time = time.time() - start
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
    def _repeat_of(b: Tuple[Tuple[int, ...], ...], sorts:int =sorts) -> int:
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
    
    for depth_e in range(0, depth+1):
        for b in _gen(tuple(min(repeat, depth) for _ in range(sorts)), depth, alts, True, depth_e):
            if _repeat_of(b) == repeat:
                yield Prefix(b, True)
    if not existentials: return
    for depth_e in range(0, depth+1):
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
                    PrefixConstraints(Logic.EPR, max_alt=1, max_repeated_sorts=2),
                    PrefixConstraints(Logic.EPR, max_alt=1, max_repeated_sorts=2),
                    PrefixConstraints(Logic.EPR, max_alt=2, max_repeated_sorts=2),
                    PrefixConstraints(Logic.EPR, max_alt=2)]
            elif logic == Logic.FOL:
                pcs = [
                    PrefixConstraints(Logic.Universal),
                    PrefixConstraints(Logic.Universal, max_repeated_sorts=2),
                    PrefixConstraints(Logic.FOL, max_alt=1, max_repeated_sorts=2),
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
                pcs = [PrefixConstraints(Logic.EPR, max_alt=2)]
            elif logic == Logic.FOL:
                pcs = [PrefixConstraints(Logic.FOL, max_alt=2)]
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

    def get_prefix(self) -> Prefix:

        if len(self._front_of_queue) > 0:
            (p, pc_index) = self._front_of_queue.pop()
            self._outstanding[p] = pc_index
            return p

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
                return candidate
        
    
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
        self._sep_problem_index = 0
        self._total_constraints_found: int = 0
        self._total_prefixes_considered: int = 0
        self._total_skipped_prefixes: int = 0
        
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


    async def check_candidate(self, checker: RobustChecker, p: Expr) -> Union[Constraint, SatResult]:
        # F_0 => p?
        initial_state = await checker.check_implication([init.expr for init in syntax.the_program.inits()], p, parallelism=2, timeout=300)
        if initial_state.result == SatResult.sat and isinstance(initial_state.trace, Trace):
            self._print("Adding initial state")
            return Pos(self.add_local_state(initial_state.trace.as_state(0)))
        elif initial_state.result == SatResult.unknown:
            self._print("Warning, implication query returned unknown")

        # F_i-1 ^ p => wp(p)?
        edge = await checker.check_transition([p, *self._frame], p, parallelism=2, timeout=300)
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
    
    async def solve(self, n_threads: int = 1, timeout: Optional[float] = None) -> Optional[Expr]:
        _log_ig_problem(self._log_prefix, self._rationale, Neg(0), list(self._reachable_constraints), self._states, self._frame, [inv for inv in syntax.the_program.invs()])

        solution: asyncio.Future[Optional[Expr]] = asyncio.Future()

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

            with ScopedProcess(_forkserver, _main_IG2_worker, self._sig, self._logs._sep_log_fname) as conn:
                # Loop over prefixes
                while True:
                    # get a prefix.
                    try:
                        prefix = self._prefix_queue.get_prefix()
                    except StopIteration:
                        self._print("Stopping worker")
                        return
                    
                    try:
                        pre_pp = " ".join(('A' if fa == True else 'E' if fa == False else 'Q') + self._sig.sort_names[sort_i] + '.' for (fa, sort_i) in prefix.linearize())
                        k_cubes = 3 if any(not fa for (fa, _) in prefix.linearize()) else 1
                        debug_this_process = False # pre_pp == 'Aquorum. Around. Around. Avalue. Avalue. Enode.'
                        
                        n_discovered_constraints = 0
                        # start a separator instance
                        worker_prefix_sent = False

                        if prefix in self._unsep_cores:
                            previous_solve_constraints: List[Constraint] = list(self._unsep_cores[prefix])
                        else:
                            previous_solve_constraints = []

                        next_constraints = list(self._necessary_constraints) + predict_useful_constraints(prefix, previous_solve_constraints)

                        start_time = time.time()
                        # logged_problem = False
                        # log_name = f"ig-{self._identity}-{self._sep_problem_index}"
                        # self._sep_problem_index += 1

                        self._print(f"Trying: {pre_pp}")
                        # Loop for adding constraints for a particular prefix
                        while True:
                            await conn.send({'constraints': send_constraints(next_constraints), 'sep': None,
                                            **({'prefix': prefix.linearize(), 'k_cubes': k_cubes, 'expt_flags': utils.args.expt_flags, 'label': self._log_prefix} if not worker_prefix_sent else {})})
                            worker_prefix_sent = True
                            # if not logged_problem and time.time() - start_time > 5:
                            #     _log_sep_problem(log_name, prefix.linearize(), next_constraints, self._states, self._frame)
                            #     logged_problem = True
                            if debug_this_process:
                                    self._print(f"Separating")
                                
                            v = await conn.recv()
                            if 'candidate' in v:
                                p, sep_constraints, (time_sep, time_eval) = cast(Expr, v['candidate']), cast(List[Constraint], v['constraints']), cast(Tuple[float, float], v['times'])
                                self._unsep_cores[prefix] = sep_constraints # share our constraints with others that may be running
                                if debug_this_process:
                                    self._print(f"Checking {p}")
                                start = time.time()
                                new_constraint_result = await self.check_candidate(checker, p)

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
                                        self._print(f"Discovered: {len(sep_constraints)}/{n_discovered_constraints} in {time.time() - start}")
                                    continue
                                elif new_constraint_result == SatResult.unsat:
                                    if not solution.done():
                                        # if utils.args.log_dir != '':
                                        #     states_needed = set(s for c in sep_constraints for s in c.states())
                                        #     structs = dict((i, s) for i, s in enumerate(self._states) if i in states_needed)
                                        #     with open(os.path.join(utils.args.log_dir, f'ig-solutions/ig-solution-{self._log_prefix}.pickle'), 'wb') as output:
                                        #         pickle.dump({'states': structs, 'constraints': sep_constraints, 'solution': p, 'prior_frame': self._frame}, output)

                                        self._prefix_queue.return_prefix(prefix)
                                        t = time.time() - start_time
                                        previous_constraints_used = len([c for c in sep_constraints if c in self._previous_constraints])
                                        self._print(f"SEP: {pre_pp} with core={len(sep_constraints)} ({n_discovered_constraints} novel, {previous_constraints_used} prev) time {t:0.3f} (sep {time_sep:0.3f}, eval {time_eval:0.3f})")
                                        self._print(f"Learned {p}")
                                        solution.set_result(p)
                                    return
                                assert False

                            elif 'unsep' in v:
                                core: List[Constraint] = v['constraints']
                                (time_sep, time_eval) = cast(Tuple[float, float], v['times'])
                                t = time.time() - start_time
                                previous_constraints_used = len([c for c in core if c in self._previous_constraints])
                                extra = ""
                                self._print(f"UNSEP: {pre_pp} with core={len(core)} ({n_discovered_constraints} novel, {previous_constraints_used} prev) time {t:0.3f} (sep {time_sep:0.3f}, eval {time_eval:0.3f}){extra}")
                                self._unsep_cores[prefix] = core
                                self._prefix_queue.complete_prefix(prefix)
                                break
                            else:
                                assert False
                    except asyncio.CancelledError:
                        self._prefix_queue.return_prefix(prefix)
                        raise

        async def logger() -> None:
            query_start = time.time()
            self._print(f"Starting IG query with timeout {timeout}")
            while True:
                try: await asyncio.sleep(30)
                except asyncio.CancelledError:
                    self._print(f"finished in: {time.time() - query_start:0.3f} sec",
                                f"constraints: {self._total_constraints_found} prefixes: {self._total_prefixes_considered} epr-skipped: {self._total_skipped_prefixes}",
                                f"({'cancelled' if solution.cancelled() else 'done'})")
                    raise
                self._print(f"time: {time.time() - query_start:0.3f} sec constraints: {self._total_constraints_found} prefixes: {self._total_prefixes_considered} epr-skipped: {self._total_skipped_prefixes}")

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
    def __init__(self, logs: Logging, parallelism: int = 1) -> None:
        self._states: List[State] = [] # List of discovered states (excluding some internal cex edges)
        self._initial_states: Set[int] = set() # States satisfying the initial conditions
        self._transitions: Set[Tuple[int, int]] = set() # Set of transitions between states (s,t)
        self._successors: DefaultDict[int, Set[int]] = defaultdict(set) # Successors t of s in s -> t
        self._predecessors: DefaultDict[int, Set[int]] = defaultdict(set) # Predecessors s of t in s -> t
        self._reachable: Set[int] = set() # Known reachable states (not necessarily including initial states)
        self._useful_reachable: Set[int] = set() # Known reachable states that violate some lemma
        
        self._lemmas: List[Expr] = [] # List of predicates discovered
        self._frame_numbers: List[Optional[int]] = [] # the frame number for each lemma
        self._initial_conditions: Set[int] = set() # predicates that are initial conditions in F_0
        self._safeties: Set[int] = set() # predicates that are safety properties
        
        self._eval_cache: Dict[Tuple[int, int], bool] = {} # Record eval for a (lemma, state)
        self._immediate_pushing_blocker: Dict[int, int] = {} # State for a lemma in F_i that prevents it pushing to F_i+1
        self._ultimate_pushing_blocker: Dict[int, Optional[Blocker]] = {} # (State, Frame) that prevents the lemma from pushing (may be an ancestor of the immediate pushing blocker, None if can't be pushed)
        self._former_pushing_blockers: DefaultDict[int, Set[int]] = defaultdict(set) # Pushing blockers from prior frames
        self._predecessor_cache: Dict[Tuple[int, int], int] = {} # For (F_i, state) gives s such that s -> state is an edge and s in F_i
        self._no_predecessors: Dict[int, Set[int]] = {} # Gives the set of predicates that block all predecessors of a state
        self._bad_lemmas: Set[int] = set() # Predicates that violate a known reachable state
        
        
        self._push_lock = asyncio.Lock()
        self._event_frame_update = asyncio.Event()
        self._logs = logs
        self._pushing_parallelism = parallelism
        
        self._push_robust_checkers: Dict[int, RobustChecker] = {}
        self._predecessor_robust_checker: RobustChecker = AdvancedChecker(syntax.the_program, self._logs._smt_log) #if 'no-advanced-checker' not in utils.args.expt_flags else ClassicChecker(self._logs._smt_log)
        
        
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


    # Adding and manipulating states, transitions, and predicates
    async def add_lemma(self, p: Expr, frame: int = 0) -> int:
        async with self._push_lock:
            i = len(self._lemmas)
            self._lemmas.append(p)
            self._frame_numbers.append(frame)
            return i
    async def add_state(self, s: State) -> int:
        i = len(self._states)
        self._states.append(s)
        # print(f"State {i} is {s[0].as_state(s[1])}")
        return i
    async def add_transition(self, a:int, b:int) -> None:
        if (a,b) in self._transitions:
            return
        self._transitions.add((a,b))
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
        yield from (index for index, f in enumerate(self._frame_numbers) if IC3Frames.frame_leq(i, f))
    def frame_transitions(self, i: FrameNum) -> Iterable[Tuple[int, int]]:
        yield from ((a, b) for a, b in self._transitions if all(self.eval(p, a) for p in self.frame_lemmas(i)))

    def print_lemmas(self) -> None:
        print ("[IC3] ---- Frame summary")
        # cnt = len([i for (i,fn) in enumerate(self._frame_numbers) if fn == 0 and i in self._bad_predicates])
        # print(f"[IC3] lemma  0 b ... (x{cnt})")
        for i, p, index in sorted(zip(self._frame_numbers, self._lemmas, range(len(self._lemmas))), key = lambda x: IC3Frames.frame_key(x[0])):
            if i == 0 and index in self._bad_lemmas:
                continue
            code = '$' if index in self._safeties else 'i' if index in self._initial_conditions else 'b' if index in self._bad_lemmas else ' '
            fn_str = f"{i:2}" if i is not None else ' +'
            print(f"[IC3] lemma {fn_str} {code} {p}")
        print(f"[IC3] Reachable states: {len(self._reachable)}, initial states: {len(self._initial_states)}")
        print("[IC3] ----")


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
            edge = await self._predecessor_robust_checker.check_transition([self._lemmas[i] for i in fp], formula_to_block, parallelism=2)
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

    def _saturate_reachability(self, state:int) -> None:
        # Mark state reachable
        if state in self._reachable:
            return
        self._reachable.add(state)
        _reachable_worklist = set([state])

        while len(_reachable_worklist) > 0:
            item = _reachable_worklist.pop()
            if item not in self._reachable:
                continue
            for b in self._successors[item]:
                if b not in self._reachable:
                    self._reachable.add(b)
                    _reachable_worklist.add(b)

    def _mark_reachable_and_bad(self, state: int) -> None:
        initial_reachable = set(self._reachable)
        self._saturate_reachability(state)
        new = self._reachable - initial_reachable
        if len(new) == 0:
            return
        print(f"Now have {len(self._reachable)} reachable states")
        # Mark any predicates as bad that don't satisfy all the reachable states
        for new_r in new:
            print(f"New reachable state: {new_r}")
            st = self._states[new_r]
            for index, p in enumerate(self._lemmas):
                if index not in self._bad_lemmas and not st.eval(p):
                    print(f"Marked {p} as bad")
                    self._bad_lemmas.add(index)
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


    # Pushing
    async def _push_once(self) -> bool:
        made_changes = False
        for index, p in sorted(enumerate(self._lemmas), key = lambda x: IC3Frames.frame_key(self._frame_numbers[x[0]])):
            # No need to push things already in F_inf or bad lemmas
            i = self._frame_numbers[index]
            if i is None or index in self._bad_lemmas:
                continue
            if index in self._immediate_pushing_blocker:
                blocker = self._immediate_pushing_blocker[index]
                # Check if blocking state is reachable (thus we should never push)
                if blocker in self._reachable:
                    assert index in self._bad_lemmas
                    continue
                # Check if the blocker state is still in F_i
                if all(self.eval(lemma, blocker) for lemma in self.frame_lemmas(i)):
                    blocker_data = Blocker(state=blocker, frame=i, lemma=index, type_is_predecessor=False)                    
                    self._ultimate_pushing_blocker[index] = await self._blockable_state(blocker_data)
                    continue
                # The blocker is invalidated
                self._former_pushing_blockers[index].add(self._immediate_pushing_blocker[index])
                del self._immediate_pushing_blocker[index]
            # Either there is no known blocker or it was just invalidated by some new lemma in F_i
            # First check if any former blockers still work
            for former_blocker in self._former_pushing_blockers[index]:
                if all(self.eval(lemma, former_blocker) for lemma in self.frame_lemmas(i)):
                    print(f"Using former blocker {former_blocker}")
                    self._immediate_pushing_blocker[index] = former_blocker
                    blocker_data = Blocker(state=former_blocker, frame=i, lemma=index, type_is_predecessor=False)
                    self._ultimate_pushing_blocker[index] = await self._blockable_state(blocker_data)
            # We found a former one to use
            if index in self._immediate_pushing_blocker:
                continue


            # Check if any new blocker exists
            # cex = check_transition(self._solver, list(self._predicates[j] for j in self.frame_predicates(i)), p, minimize=False)
            fp = set(self.frame_lemmas(i))
            if index not in self._push_robust_checkers:
                self._push_robust_checkers[index] = AdvancedChecker(syntax.the_program, self._logs._smt_log) # if 'no-advanced-checker' not in utils.args.expt_flags else ClassicChecker(self._logs._smt_log)
            # cex = await robust_check_transition(list(self._predicates[j] for j in fp), p, minimize='no-minimize-block' not in utils.args.expt_flags, parallelism=self._threads_per_ig, log=self._logs._smt_log)
            cex = await self._push_robust_checkers[index].check_transition(list(self._lemmas[j] for j in fp), p, parallelism=self._pushing_parallelism)
            if fp != set(self.frame_lemmas(i)):
                # Set of predicates changed across the await call. To avoid breaking the meta-invariant, loop around for another iteration
                made_changes = True
                continue
            if cex.result == SatResult.unsat:
                print(f"Pushed {p} to frame {i+1}")
                self._frame_numbers[index] = i + 1
                self._event_frame_update.set()
                self._event_frame_update.clear()
                made_changes = True
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
            else:
                print(f"cex {cex.result}")
                assert False
        return made_changes

    def _check_for_f_infinity(self) -> bool:
        made_changes = False
        for i in range(max(x for x in self._frame_numbers if x is not None)):
            # Check to see if any frame
            if i in self._frame_numbers:
                continue
            # Frame has no predicates that aren't also in later frames. Move any such predicates to F_inf
            for index, p in enumerate(self._lemmas):
                p_frame = self._frame_numbers[index]
                if p_frame is not None and i < p_frame:
                    print(f"Pushed {p} to frame inf")
                    self._frame_numbers[index] = None
                    made_changes = True
        return made_changes

    async def wait_for_frame_update(self) -> None:
        await self._event_frame_update.wait()

    async def push(self) -> None:
        async with self._push_lock:
            start = time.time()
            while True:
                pushed = await self._push_once()
                made_infinite = self._check_for_f_infinity()
                # We did something, so go see if more can happen
                if pushed or made_infinite:
                    continue
                break
            print(f"Pushing completed in {time.time() - start:0.3f} sec")

    async def get_blocker(self, lemm: int) -> Optional[Blocker]:
        async with self._push_lock:
            if self._frame_numbers[lemm] is None or lemm in self._bad_lemmas:
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
                edge = await self._predecessor_robust_checker.check_transition([*(self._lemmas[i] for i in fp), l], formula_to_block, parallelism=2)
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

        while True:
            fp = set(self.frame_lemmas(i))
            if lemm not in self._push_robust_checkers:
                self._push_robust_checkers[lemm] = AdvancedChecker(syntax.the_program, self._logs._smt_log) # if 'no-advanced-checker' not in utils.args.expt_flags else ClassicChecker(self._logs._smt_log)
            
            cex = await self._push_robust_checkers[lemm].check_transition([*(self._lemmas[j] for j in fp), l], p, parallelism=self._pushing_parallelism)
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
                self._former_pushing_blockers[lemm].add(blocker)
                blocker_data = Blocker(state=blocker, frame=i, lemma=lemm, type_is_predecessor=False)
                actual_blocker = await self._blockable_state(blocker_data)
                if actual_blocker is None:
                    print("Didn't speculate because blocker is reachable")
                    return None                    
                if actual_blocker.frame != i:
                    print("Speculating with actual blocker in another frame")
                    # return None
                return blocker_data
            else:
                print(f"cex {cex.result}")
                assert False

class ParallelFolIc3:
    FrameNum = Optional[int]
    def __init__(self) -> None:
        self._sig = prog_to_sig(syntax.the_program, two_state=False)
        
        self._unsafe: bool = False # Is the system unsafe? Used for termination TODO: actually set this flag
        
        thread_budget = utils.args.cpus if utils.args.cpus is not None else 10
        self._threads_per_ig = max(1, thread_budget//2) if 'no-heuristic-pushing' not in utils.args.expt_flags else thread_budget
        self._logs = Logging(utils.args.log_dir)
       
        self._current_push_heuristic_tasks: Set[Tuple[int,int]] = set() # Which (frame, state) pairs are being worked on by the push heuristic?
        self._frames = IC3Frames(self._logs, self._threads_per_ig)
        
        # Logging, etc
        self._start_time: float = 0
        self._logs = Logging(utils.args.log_dir)
        self._next_ig_query_index = 0

    # Termination conditions
    def is_complete(self) -> bool:
        return self.is_program_safe() or self.is_program_unsafe()
    def is_program_safe(self) -> bool:
        # Safe if all safeties have been pushed to F_inf
        return all(self._frames._frame_numbers[i] is None for i in self._frames._safeties)
    def is_program_unsafe(self) -> bool:
        return self._unsafe

    def print_frames(self) -> None:
        self._frames.print_lemmas()
        print(f"time: {time.time() - self._start_time:0.3f} sec")

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

    async def parallel_inductive_generalize(self, b: Blocker, rationale: str = '', timeout: Optional[float] = None, prior_solver: Optional[IGSolver] = None) -> IGSolver:
        ig_frame = set(self._frames.frame_lemmas(b.frame-1))
        ig_solver = IGSolver(self._frames._states[b.state],
                                  [self._frames._states[x] for x in self._frames._useful_reachable | self._frames._initial_states],
                                  [self._frames._lemmas[x] for x in ig_frame],
                                  self._logs, syntax.the_program, rationale, self._next_ig_query_index, prior_solver)
        self._next_ig_query_index += 1
        
        negative_states = set([b.state])
        sol: asyncio.Future[Optional[Expr]] = asyncio.Future()
        async with ScopedTasks() as tasks:
            async def frame_updater()-> None:
                while True:
                    current_frame = set(self._frames.frame_lemmas(b.frame-1))
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

            async def solver() -> None:
                main_solve_start = time.time()
                p = await ig_solver.solve(self._threads_per_ig, timeout = timeout)
                main_solve_time = time.time() - main_solve_start

                if p is None:
                    if not sol.done():
                        sol.set_result(None)
                    return

                if 'no-multi-generalize' not in utils.args.expt_flags:
                    time_to_generalize = 4.0 * main_solve_time + 1
                    generalizations_found = 0
                    while True:
                        gen_solve_start = time.time()
                        if p is None:
                            break
                        new_blocker = await self._frames.speculative_push(p, b.frame, b)
                        if new_blocker is None:
                            break
                        
                        # The new state should satisfy the current candidate p
                        assert eval_predicate(self._frames._states[new_blocker.state], p)

                        negative_states.add(new_blocker.state)
                        ig_solver.add_negative_state(self._frames._states[new_blocker.state])
                        new_p = await ig_solver.solve(self._threads_per_ig, timeout = time_to_generalize)
                        if new_p is None:
                            print("Failed to find generalized lemma in time")
                            break
                        p = new_p
                        print(f"Generalized to {p}")
                        generalizations_found += 1
                        gen_solve_end = time.time()
                        time_to_generalize -= gen_solve_end-gen_solve_start
                        if time_to_generalize < 0.005: break
                    print(f"Generalized a total of {generalizations_found} times")

                if not sol.done():
                    sol.set_result(p)

            tasks.add(frame_updater())
            tasks.add(concurrent_block())
            tasks.add(solver())
            final_p = await sol

        if final_p is None:
            print(f"IG query cancelled ({b.state} in frame {b.frame} for {rationale})")
            return ig_solver

        print(f"Learned new lemma {final_p} blocking {b.state} in frame {b.frame} for {rationale}")
        await self._frames.add_lemma(final_p, b.frame)
        await self._frames.push()
        self.print_frames()
        return ig_solver

    def heuristic_priority(self, pred: int) -> Any:
        def mat_size(e: Expr) -> int:
            if isinstance(e, QuantifierExpr): return mat_size(e.body)
            elif isinstance(e, UnaryExpr): return mat_size(e.arg)
            elif isinstance(e, NaryExpr): return sum(map(mat_size, e.args))
            else: return 1
        fn = self._frames._frame_numbers[pred]
        return (-fn if fn is not None else 0, mat_size(self._frames._lemmas[pred]) + random.random() * 0.5)

    async def heuristic_pushing_to_the_top_worker(self) -> None:
        # print("Starting heuristics")
        timeouts = [100.0, 500.0, 2000.0]
        timeout_index = 0
        current_timeout: Dict[Tuple[int, int], int] = {}
        while True:
            priorities = sorted(range(len(self._frames._lemmas)), key=self.heuristic_priority)
            # print("Checking for something to do")
            frame_N = min((self._frames._frame_numbers[s] for s in self._frames._safeties), key = IC3Frames.frame_key)
            # print(f"Frame_N: {frame_N}")
            # print(f"Finding task with index {timeout_index}")
            for pred in priorities:
                # Don't push anything past the earliest safety
                if IC3Frames.frame_leq(frame_N, self._frames._frame_numbers[pred]):
                    continue
                # if not self.heuristically_blockable(pred):
                #     continue
                blocker = await self._frames.get_blocker(pred)
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
                    print(f"Heuristically blocking state {st} in frame {fn} timeout {timeout}")
                    await self.parallel_inductive_generalize(blocker, 'heuristic-push', timeout=timeout)
                    
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
                    if self._frames._frame_numbers[safety] is not None:
                        print("Safety Violation!")
                        self._unsafe = True
                    return
                new_solver = await self.parallel_inductive_generalize(blockable, rationale="learning", timeout = None, prior_solver = prior_solver)                
                prior_solver = new_solver
                break
            else:
                return

    async def run(self) -> None:
        self._start_time = time.time()
        await self.init()
        await self._frames.push()
        self.print_frames()
        async with ScopedTasks() as tasks:
            if 'no-heuristic-pushing' not in utils.args.expt_flags:
                tasks.add(self.heuristic_pushing_to_the_top_worker())
            # tasks.add(self.inexpensive_reachability())
            tasks.add(self.learn())
            while not self.is_complete():
                await self._frames.wait_for_frame_update()

        print(f"Elapsed: {time.time() - self._start_time:0.2f} sec")
        if self.is_program_safe():
            print("Program is SAFE.")
            for frame, (index, p) in zip(self._frames._frame_numbers, enumerate(self._frames._lemmas)):
                if frame is None and index not in self._frames._safeties:
                    print(f"  invariant [inferred] {p}")
        elif self.is_program_unsafe():
            print("Program is UNSAFE.")
        else:
            print("Program is UNKNOWN.")

def p_fol_ic3(_: Solver) -> None:
    # Redirect stdout if we have a log directory
    if utils.args.log_dir:
        os.makedirs(utils.args.log_dir, exist_ok=True)
        for dir in ['smt-queries', 'ig-problems', 'sep-unsep', 'sep-problems', 'eval']:
            os.makedirs(os.path.join(utils.args.log_dir, dir), exist_ok=True)
        sys.stdout = io.TextIOWrapper(open(os.path.join(utils.args.log_dir, "main.log"), "wb"), line_buffering=True, encoding='utf8')

    # Print initial header with command line
    print(f"ParallelFolIC3 log for {os.path.basename(utils.args.filename)}")
    print(f"Command line: {' '.join(sys.argv)}")

    global _forkserver
    _forkserver = ForkServer()
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
        for x in prog.invs():
            if x.is_safety: continue
            conjuncts += 1
            quants = max(quants, count_quantifiers(x.expr))
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
        if has_exists:
            if networkx.is_directed_acyclic_graph(g):
                print('--logic=epr', '--epr-edges=' + repr(','.join(f'{a}->{b}' for a,b in edges2)), utils.args.filename)
            else:
                print('--logic=fol', utils.args.filename)
        else:
            print('--logic=universal', utils.args.filename)
    

def fol_learn(solver: Solver) -> None:
    # global _forkserver
    # _forkserver = ForkServer()
    # async def main() -> None:
    #     sig = prog_to_sig(syntax.the_program)
    #     golden = list(syntax.the_program.invs())[utils.args.index].expr
    #     print("Target:", golden)
    #     def all_prefixes() -> Iterator[Prefix]:
    #         for d in range(1000):
    #             for alts in range(d):
    #                 yield from generate_exclusive(len(sig.sort_indices), d, alts, 4, True)
    #     pc = PrefixConstraints()
    #     if utils.args.logic == 'epr':
    #         pc.logic = Logic.EPR
    #     else:
    #         pc.logic = Logic.FOL
    #     constraints: List[Union[Pos, Neg]] = []
    #     states: List[State] = []
    #     prefixes = all_prefixes()
    #     while True:
    #         prefix = next(prefixes)
    #         print("Trying ", prefix.linearize())
    #         sep = FixedImplicationSeparatorPyCryptoSat(sig, prefix.linearize(), pc = pc, k_cubes=3)
    #         to_sep = {}
    #         current_constraints = set()
    #         def add_constraint(c: Union[Neg, Pos]) -> None:
    #             if c in current_constraints: return
    #             if c.i not in to_sep:
    #                 to_sep[c.i] = sep.add_model(state_to_model(states[c.i]))
    #             sep.add_constraint(c.map(to_sep))
    #             current_constraints.add(c)        
    #         while True:
    #             p = sep.separate(minimize=True)
    #             if p is None:
    #                 break
    #             with syntax.the_program.scope.n_states(1):
    #                 pp = formula_to_predicate(p, syntax.the_program.scope)
    #             print("Separator:", pp)
    #             for c in constraints:
    #                 if not satisifies_constraint(c, pp, states):
    #                     add_constraint(c)
    #                     break
    #             else:
    #                 query_r = await robust_check_implication([pp], golden)
    #                 if isinstance(query_r, Trace):
    #                     i = len(states)
    #                     states.append(query_r.as_state(0))
    #                     constraints.append(Neg(i))
    #                     add_constraint(Neg(i))
    #                     print("Added negative constraint")
    #                     continue
    #                 query_r = await robust_check_implication([golden], pp)
    #                 if isinstance(query_r, Trace):
    #                     i = len(states)
    #                     states.append(query_r.as_state(0))
    #                     constraints.append(Pos(i))
    #                     add_constraint(Pos(i))
    #                     print("Added positive constraint")
    #                     continue
    #                 print("Matches")
    #                 return
    # asyncio.run(main())
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
                print("sat ", end ='', flush=True)
                m = s.model()
                random.shuffle(assertions)
                for i, a in enumerate(assertions):
                    if not z3.is_true(m.eval(a, model_completion=True)):
                        print(f"adding {i} ", end ='', flush=True)
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
            pass # print(f"{expr}")
    
    else:
        assert False

def fol_benchmark_solver(_: Solver) -> None:
    global _forkserver
    _forkserver = ForkServer()
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
        start_time = time.time()
        checker = AdvancedChecker(syntax.the_program)
        r_r = asyncio.run(checker.check_transition(old_hyps, new_conc, 1, 1000000.0))
        end_time = time.time()
        print (r_r.result)
        print (f"=== Solution obtained in {end_time-start_time:0.3f}")

        # print(checker._last_successful)
        # print(checker._transitions)

        start_time = time.time()
        r_r = asyncio.run(checker.check_transition(old_hyps, new_conc, 1, 1000000.0))
        end_time = time.time()
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

            start = time.time()
            print(p)
            for key, st in states.items():
                print(st.eval(p), ','.join(f'{len(l)}' for l in st.univs.values()))
            end = time.time()
            print(f"elapsed: {end-start:0.3f}")
            total += end-start
    print(f"overall: {total:0.3f}")


def fol_debug_ig(_: Solver) -> None:
    global _forkserver
    _forkserver = ForkServer()
    async def main() -> None:
        # if utils.args.output:
        #     sys.stdout = open(utils.args.output, "w")
        print(f"Benchmarking {utils.args.query} ({utils.args.filename})")
        data = pickle.load(open(utils.args.query, 'rb'))
        (rationale, block, pos, states, prior_frame, golden) = data
        
        print(f"Results for IG query {utils.args.query} {rationale}")
        
        state_to_block: State = states[block.i]
        for human_inv in syntax.the_program.invs():
            i = human_inv.expr
            if not state_to_block.eval(i):
                print(f"{i} is a candidate solution")
                checker = AdvancedChecker(syntax.the_program)
                res = await checker.check_transition(prior_frame + [i], i, parallelism=10, timeout=500)
                if res.result == SatResult.unsat:
                    print("relatively inductive (solution)")
                elif res.result == SatResult.unknown:
                    print("relative inductiveness unknown")
                else:
                    print("not relatively inductive (not solution)")
    asyncio.run(main())
    
    
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
    s.add_argument("--log-dir", dest="log_dir", type=str, default="", help="Log directory")
    s.add_argument("--inv", dest="inv", type=str, default="", help="Invariant name")
    result.append(s)

    s = subparsers.add_parser('fol-benchmark-solver', help='Test SMT solver backend')
    s.set_defaults(main=fol_benchmark_solver)
    s.add_argument("--query", type=str, help="Query to benchmark")
    s.add_argument("--output", type=str, help="Output to file")
    s.add_argument("--log-dir", dest="log_dir", type=str, default="", help="Log directory")
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

    s = subparsers.add_parser('fol-benchmark-eval', help='Test formula evaluation performance')
    s.set_defaults(main=fol_benchmark_eval)
    s.add_argument("--query", type=str, help="Query to benchmark")
    s.add_argument("--output", type=str, help="Output to file")
    s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: set(x.split(',')), default=set(), help="Experimental flags")
    result.append(s)

    s = subparsers.add_parser('fol-debug-ig', help='Debug a IG solution')
    s.set_defaults(main=fol_debug_ig)
    s.add_argument("--query", type=str, help="Solution to query")
    s.add_argument("--epr-edges", dest="epr_edges", type=epr_edges, default=[], help="Allowed EPR edges in inferred formula")
    s.add_argument("--expt-flags", dest="expt_flags", type=lambda x: set(x.split(',')), default=set(), help="Experimental flags")
    s.add_argument("--log-dir", dest="log_dir", type=str, default="", help="Log directory")
    # s.add_argument("--output", type=str, help="Output to file")
    result.append(s)

    return result
