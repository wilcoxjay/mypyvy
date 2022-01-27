

from typing import Any, Callable, Dict, Iterable, Protocol, TextIO, List, Optional, Tuple, Union, cast, Set, Sequence
import sys, os, asyncio, pickle, time, random, functools, copyreg
from dataclasses import dataclass, field

from async_tools import AsyncConnection, FileDescriptor, ScopedProcess, ScopedTasks, get_forkserver

from logic import Expr, Solver, Trace
from syntax import New, Not, Program, TrueExpr, DefinitionDecl
import syntax
from solver_cvc5 import CVC5Solver, SatResult
from translator import Z3Translator
import utils
import z3

@dataclass
class RobustCheckResult:
    result: SatResult
    trace: Optional[Trace] = None
    core: Set[int] = field(default_factory=set)
    transition: Optional[str] = None
    # time: float = 0.0

class RobustChecker(Protocol):
    _all_queries: List[Tuple[List[Expr], Expr]]
    async def check_implication(self, hyps: Iterable[Expr], conc: Expr, parallelism: int = 1, timeout: float = 0.0) -> RobustCheckResult: ...
    async def check_transition(self, hyps: Iterable[Expr], conc: Expr, parallelism: int = 1, timeout: float = 0.0) -> RobustCheckResult: ...


def _fancy_check_transition2_internal(hyps: List[Expr], new_conc: Expr, tr: Expr, timeout: float = 1.0, _print: Callable = print) -> Union[List[int], None, Trace]:
    sat_inst = z3.Optimize()
    for i in range(len(hyps)):
        sat_inst.add_soft(z3.Not(z3.Bool(f'I_{i}')))
    # sat_inst.add(z3.Bool('I_0'))
    # order: List[int] = []
    badness = [0 for _ in range(len(hyps))]
    unknown_count = 0
    while True:
        solver = CVC5Solver(syntax.the_program, timeout=int(timeout * 1000))
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
                    to_add_possibilities.sort(key=lambda i: badness[i])
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
                elif r is None:
                    await conn.send(RobustCheckResult(SatResult.unknown))
                else:
                    await conn.send(RobustCheckResult(SatResult.unsat, core=set(r)))
            elif v['solver'] == 'z3-basic' or v['solver'] == 'cvc4-basic':
                s = Solver(use_cvc4=v['solver'] == 'cvc4-basic')
                t = s.get_translator(2)
                with s.new_frame():
                    for i in expr_ids:
                        s.add(t.translate_expr(exprs[i]))
                    s.add(t.translate_expr(tr))
                    s.add(t.translate_expr(New(Not(conc))))
                    raw_result = s.check(timeout=min(1000000000, int(timeout * 1000)))
                    if raw_result == z3.unsat:
                        await conn.send(RobustCheckResult(SatResult.unsat, core=set(range(len(expr_ids)))))
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
                        await conn.send(RobustCheckResult(SatResult.unsat, core=set(range(len(expr_ids)))))
                    elif raw_result5 == SatResult.sat:
                        await conn.send(RobustCheckResult(SatResult.sat, s5.get_trace()))
                    else:
                        await conn.send(RobustCheckResult(SatResult.unknown))
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
                    raw_result = s.check(timeout=min(1000000000, int(timeout * 1000)))
                    if raw_result == z3.unsat:
                        await conn.send(RobustCheckResult(SatResult.unsat, core=set(range(len(expr_ids)))))
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
                        await conn.send(RobustCheckResult(SatResult.unsat, core=set(range(len(expr_ids)))))
                    elif raw_result5 == SatResult.sat:
                        await conn.send(RobustCheckResult(SatResult.sat, s5.get_trace()))
                    else:
                        await conn.send(RobustCheckResult(SatResult.unknown))
                del s5

_robust_id = 0
def _get_robust_id() -> str:
    global _robust_id
    id = f'{_robust_id:06d}'
    _robust_id += 1
    return id

class AdvancedChecker(RobustChecker):
    def __init__(self, prog: Program, log: TextIO = sys.stdout) -> None:
        self._prog = prog
        self._log = log
        self._transitions: List[str] = [tr.name for tr in self._prog.transitions()]
        self._tr_formulas = {tr.name: tr.as_twostate_formula(self._prog.scope) for tr in self._prog.transitions()}
        self._last_successful: Dict[str, Tuple[str, float, float]] = {}
        self._log_id = _get_robust_id()
        self._query_id = 0
        self._all_queries: List[Tuple[List[Expr], Expr]] = []

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
        strategies = [('z3-basic', 0.25), ('cvc5-basic', 0.5), ('z3-basic', 2.0), ('cvc5-basic', 5.0), ('z3-basic', 10.0), ('cvc5-basic', 20.0)]

        def get_next_attempt() -> Iterable[Tuple[str, float]]:
            for attempt in range(1000000):
                yield strategies[min(len(strategies) - 1, attempt)]
        strategy_gen = iter(get_next_attempt())

        async def worker() -> None:
            while not result.done():
                try:
                    with ScopedProcess(get_forkserver(), _main_worker_advanced_implication, FileDescriptor(self._log.fileno()), log_prefix) as conn:
                        await conn.send({'exprs': {i: formulas[i] for i in range(len(formulas))}})
                        while not result.done():
                            (solver_type, timeout) = next(strategy_gen)
                            await conn.send({'solve': (list(range(len(formulas))), timeout), 'solver': solver_type})
                            resp: RobustCheckResult = await asyncio.wait_for(conn.recv(), timeout + 1)
                            if resp.result == SatResult.unsat:
                                if not result.done():
                                    result.set_result(RobustCheckResult(SatResult.unsat, core=resp.core))
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
                start = time.perf_counter()
                for i in range(parallelism):
                    tasks.add(worker())
                tasks.add(logger())
                rr = await asyncio.wait_for(result, timeout if timeout > 0 else None)
                self._print(log_prefix, f"Completed implication {rr.result} in {time.perf_counter() - start:0.3f}")
                return rr
        except asyncio.TimeoutError:
            self._print(log_prefix, "Implication query timed out")
            return RobustCheckResult(SatResult.unknown)

    async def check_transition(self, _hyps: Iterable[Expr], conc: Expr, parallelism: int = 1, timeout: float = 0.0) -> RobustCheckResult:
        log_prefix = self._get_log_prefix()
        hyps = list(_hyps)
        trs_unsat: Dict[str, Set[int]] = {}
        attempts_started = {tr.name: 0 for tr in self._prog.transitions()}
        result: asyncio.Future[RobustCheckResult] = asyncio.Future()
        self._all_queries.append((hyps, conc))
        # strategies = [('cvc5-basic', 0.5), ('z3-basic', 0.25), ('cvc5-fancy', 15.0), ('z3-basic', 5.0), ('cvc5-fancy', 30.0), ('z3-basic', 5.0), ('cvc5-fancy', 45.0)]
        # strategies = [('cvc5-fancy', 100000.0)]
        strategies = [('cvc5-basic', 0.5, 0), ('z3-basic', 0.25, 0), ('cvc5-fancy', 20.0, 2), ('cvc5-fancy', 400.0, 16), ('cvc5-fancy', 1600.0, 64)]

        def get_next_attempt() -> Iterable[Tuple[str, Tuple[str, float, float]]]:
            while True:
                for tr in self._transitions:
                    if tr not in trs_unsat:
                        attempt_num = attempts_started[tr]
                        attempts_started[tr] += 1
                        if attempt_num == 0 and tr in self._last_successful:
                            st = self._last_successful[tr]
                        elif tr in self._last_successful:
                            st = strategies[min(len(strategies) - 1, attempt_num - 1)]
                        else:
                            st = strategies[min(len(strategies) - 1, attempt_num)]
                        yield (tr, st)
        strategy_gen = iter(get_next_attempt())

        async def worker() -> None:
            while not result.done():
                try:
                    with ScopedProcess(get_forkserver(), _main_worker_advanced_transition, FileDescriptor(self._log.fileno()), log_prefix) as conn:
                        await conn.send({'exprs': {i: hyps[i] for i in range(len(hyps))}})
                        while not result.done():
                            (tr, (solver_type, timeout, unk_timeout)) = next(strategy_gen)
                            await conn.send({'formulas': (self._tr_formulas[tr], conc), 'tr-name': tr, 'solve': (list(range(len(hyps))), timeout), 'solver': solver_type, 'unk_timeout': unk_timeout})
                            resp: RobustCheckResult = await asyncio.wait_for(conn.recv(), timeout + 1)
                            # Save the success solver type for this transition so it is tried first next time
                            if resp.result != SatResult.unknown:
                                self._last_successful[tr] = (solver_type, timeout, unk_timeout)
                            if resp.result == SatResult.unsat:
                                trs_unsat[tr] = resp.core
                                if len(trs_unsat) == len(self._transitions) and not result.done():
                                    result.set_result(RobustCheckResult(SatResult.unsat, core=cast(Set[int], set()).union(*trs_unsat.values())))
                            if resp.result == SatResult.sat:
                                self._transitions = [tr, *(t for t in self._transitions if t != tr)]
                                resp.transition = tr
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
                start = time.perf_counter()
                for i in range(parallelism):
                    tasks.add(worker())
                tasks.add(logger())
                rr = await asyncio.wait_for(result, timeout if timeout > 0 else None)
                self._print(log_prefix, f"Completed transition {rr.result} in {time.perf_counter() - start:0.3f}")
                return rr
        except asyncio.TimeoutError:
            self._print(log_prefix, "Transition query timed out")
            return RobustCheckResult(SatResult.unknown)

# This is a class designed to cache the result of pickling.
# This helps the main process which needs to serialize lemmas many times in robust_check_implication
# It deserializes directly into the underlying Expr. This caching relies on Exprs being immutable.
class _TopLevelExpr:
    def __init__(self, v: Expr):
        self.v = v
        self.cache: Optional[bytes] = None
    def reduce(self) -> Tuple[Any, Tuple]:
        if self.cache is None:
            self.cache = pickle.dumps(self.v)
        return pickle.loads, (self.cache,)
copyreg.pickle(_TopLevelExpr, cast(Any, _TopLevelExpr.reduce))


async def _main_robust_check_worker(conn: AsyncConnection, n_states: int) -> None:
    s_z3 = Solver(use_cvc4=False)
    s_cvc4 = Solver(use_cvc4=True)
    t = s_z3.get_translator(n_states)
    t2 = s_cvc4.get_translator(n_states)
    while True:
        try:
            (exprs, use_cvc4, time_limit) = cast(Tuple[List[Expr], bool, float], await conn.recv())
        except EOFError:
            return
        s = s_cvc4 if use_cvc4 else s_z3
        with s.new_frame():
            for e in exprs:
                if not use_cvc4:
                    s.add(t.translate_expr(e))
                else:
                    s.add(t2.translate_expr(e))
            # print(f"{prefix} _robust_check(): checking ({f_i}, {count}, {use_cvc4}) in {time_limit}", file=log)
            # print(s.assertions())
            r = s.check(timeout = min(1000000000, int(time_limit * 1000)))
            # print(f"{prefix} _robust_check(): r = {r}", file=log)
            # to ignore z3 models
            if not use_cvc4 and r == z3.sat:
                r = z3.unknown
            tr = Z3Translator.model_to_trace(s.model(minimize=True), n_states) if r == z3.sat else r
        await conn.send(tr)


async def _robust_check(formulas: Sequence[Callable[[], Iterable[Union[Expr, _TopLevelExpr]]]], n_states: int = 1, parallelism: int = 1, timeout: float = 0.0, log: TextIO = sys.stdout, prefix: str = '') -> Union[Trace, z3.CheckSatResult]:
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
    _running: int = parallelism
    async def _manager() -> None:
        nonlocal _running
        while True:
            with ScopedProcess(get_forkserver(), _main_robust_check_worker, n_states) as conn:
                try:
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
                        (f_i, index, use_cvc4, timeout) = v
                        v_prime: Tuple[List[Union[Expr, _TopLevelExpr]], bool, float] = (list(formulas[f_i]()), use_cvc4, timeout)
                        await conn.send(v_prime)
                        start = time.perf_counter()
                        try:
                            r = await asyncio.wait_for(conn.recv(), timeout + 1)
                        except asyncio.TimeoutError:
                            end = time.perf_counter()
                            print(f"{prefix} attempt (F_{f_i} i={index} {'cvc4' if use_cvc4 else 'z3'} to={timeout}) aborted due to solver over time in {end-start:0.3f}", file=log)
                            break
                        end = time.perf_counter()
                        print(f"{prefix} attempt (F_{f_i} i={index} {'cvc4' if use_cvc4 else 'z3'} to={timeout}) returned {z3.sat if isinstance(r, Trace) else r} in {end-start:0.3f}", file=log)
                        if r == z3.unsat:
                            formulas_unsat.add(f_i)
                        elif isinstance(r, Trace):
                            if not result.done():
                                result.set_result(r)
                            return
                except EOFError:
                    print(f"{prefix} solver process ended", file=log)
            print(f"{prefix} restarting solver proc", file=log)

    async with ScopedTasks() as tasks:
        for _ in range(parallelism):
            tasks.add(_manager())
        return await result

async def _robust_check_transition(old_hyps: Iterable[Expr], new_conc: Expr, minimize: Optional[bool] = None, transition: Optional[DefinitionDecl] = None, parallelism: int = 1, timeout: float = 0.0, log: TextIO = sys.stdout) -> Union[Trace, z3.CheckSatResult]:
    id = _get_robust_id()
    log_prefix = f'[Tr-{id}]'
    start = time.perf_counter()
    r: Union[Trace, z3.CheckSatResult, None] = None
    try:
        transitions = list(syntax.the_program.transitions())
        tr_formulas = [_TopLevelExpr(transition.as_twostate_formula(syntax.the_program.scope)) for transition in transitions]
        new_formula = _TopLevelExpr(New(Not(new_conc)))
        old_hyp_formulas = [_TopLevelExpr(h) for h in old_hyps]
        
        def make_formula(i: int) -> Iterable[Union[Expr, _TopLevelExpr]]:
            yield from [new_formula, tr_formulas[i]]
            exprs = list(old_hyp_formulas)
            random.shuffle(exprs)
            yield from exprs
        formulas = [functools.partial(make_formula, i) for i in range(len(transitions))]
        r = await _robust_check(formulas, 2, parallelism=parallelism, timeout=timeout, log=log, prefix=log_prefix)
        return r
    finally:
        elapsed = time.perf_counter() - start
        res = 'unsat' if r == z3.unsat else 'sat' if isinstance(r, Trace) else 'unk' if r == z3.unknown else 'int'
        if elapsed > 5 and utils.args.log_dir != '':
            fname = f'tr-query-{id}-{res}-{int(elapsed):04d}.pickle'
            with open(os.path.join(utils.args.log_dir, 'smt-queries', fname), 'wb') as f:
                pickle.dump((old_hyps, new_conc, minimize, transition.name if transition is not None else None), f, protocol=pickle.HIGHEST_PROTOCOL)
            print(log_prefix, f'transition query result {res} took {elapsed:0.3f} log {fname}', file=log)
        else:
            print(log_prefix, f'transition query result {res} took {elapsed:0.3f}', file=log)

async def _robust_check_implication(hyps: Iterable[Expr], conc: Expr, minimize: Optional[bool] = None, parallelism: int = 1, timeout: float = 0.0, log: TextIO = sys.stdout) -> Union[Trace, z3.CheckSatResult]:
    id = _get_robust_id()
    log_prefix = f'[Im-{id}]'
    start = time.perf_counter()
    r: Union[Trace, z3.CheckSatResult, None] = None
    try:
        def make_formula() -> Iterable[Expr]:
            yield Not(conc)
            hs = list(hyps)
            random.shuffle(hs)
            yield from hs
        r = await _robust_check([make_formula], 1, parallelism=parallelism, timeout=timeout, log=log, prefix=log_prefix)
        return r
    finally:
        elapsed = time.perf_counter() - start
        res = 'unsat' if r == z3.unsat else 'sat' if isinstance(r, Trace) else 'unk' if r == z3.unknown else 'int'
        if elapsed > 5 and utils.args.log_dir != '':
            fname = f'im-query-{id}-{res}-{int(elapsed):04d}.pickle'
            with open(os.path.join(utils.args.log_dir, 'smt-queries', fname), 'wb') as f:
                pickle.dump((hyps, conc, minimize), f, protocol=pickle.HIGHEST_PROTOCOL)
            print(log_prefix, f'implication query result {res} took {elapsed:0.3f} log {fname}', file=log)
        else:
            print(log_prefix, f'implication query result {res} took {elapsed:0.3f}', file=log)

def _robust_result_from_z3_or_trace(hyps: Iterable, r: Union[z3.CheckSatResult, Trace]) -> 'RobustCheckResult':
    if isinstance(r, Trace):
        return RobustCheckResult(SatResult.sat, r)
    elif r == z3.unsat:
        return RobustCheckResult(SatResult.unsat, core=set(range(len(list(hyps)))))
    else:
        return RobustCheckResult(SatResult.unknown, None)

class ClassicChecker(RobustChecker):
    def __init__(self, log: TextIO = sys.stdout) -> None:
        self._log = log
        self._all_queries: List[Tuple[List[Expr], Expr]] = []
    
    async def check_implication(self, hyps: Iterable[Expr], conc: Expr, parallelism: int = 1, timeout: float = 0.0) -> RobustCheckResult:
        return _robust_result_from_z3_or_trace(hyps, await _robust_check_implication(hyps, conc, parallelism=parallelism, timeout=timeout, log=self._log))
    
    async def check_transition(self, _hyps: Iterable[Expr], conc: Expr, parallelism: int = 1, timeout: float = 0.0) -> RobustCheckResult:
        hyps = list(_hyps)
        self._all_queries.append((hyps, conc))
        return _robust_result_from_z3_or_trace(hyps, await _robust_check_transition(hyps, conc, parallelism=parallelism, timeout=timeout, log=self._log))
