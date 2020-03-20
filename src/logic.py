from __future__ import annotations
from collections import OrderedDict, defaultdict
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime
import dataclasses
import time
import itertools
import io
import re
import sexp
import subprocess
import sys
import typing
from typing import List, Any, Optional, Set, Tuple, Union, Iterable, Dict, Sequence, Iterator, \
    cast, TypeVar, Callable
from types import TracebackType
import z3

import utils
from utils import MySet
import syntax
from syntax import Expr, Scope, ConstantDecl, RelationDecl, SortDecl, \
    FunctionDecl, DefinitionDecl, Program

z3.Forall = z3.ForAll

KEY_ONE = 'one'
KEY_NEW = 'new'
KEY_OLD = 'old'
TRANSITION_INDICATOR = 'tid'

# useful for debugging
def verbose_print_z3_model(m: z3.ModelRef) -> None:
    utils.logger.always_print('')
    out = io.StringIO()
    fmt = z3.Formatter()  # type: ignore
    fmt.max_args = 10000
    utils.logger.always_print(str(fmt.max_args))
    pp = z3.PP()  # type: ignore
    pp.max_lines = 10000
    pp(out, fmt(m))
    utils.logger.always_print(out.getvalue())
    assert False

def check_solver(s: Solver, keys: Tuple[str, ...], minimize: Optional[bool] = None) -> Optional[Trace]:
    res = s.check()
    m = None

    if res != z3.unsat:
        if res != z3.sat:
            assert res == z3.unknown
            utils.logger.always_print('unknown!')
            utils.logger.always_print('reason unknown: ' + s.reason_unknown())
            assert False, 'unexpected unknown from z3!'

        assert res == z3.sat
        m = Trace.from_z3(keys, s.model(minimize=minimize))

    return m

def check_unsat(
        errmsgs: List[Tuple[Optional[syntax.Span], str]],
        s: Solver,
        keys: Tuple[str, ...]
) -> Optional[Trace]:
    start = datetime.now()
    # if logger.isEnabledFor(logging.DEBUG):
    #     logger.debug('assertions')
    #     logger.debug(str(s.assertions()))

    if (m := check_solver(s, keys)) is not None:
        utils.logger.always_print('')
        if utils.args.print_counterexample:
            utils.logger.always_print(str(m))

        for span, msg in errmsgs:
            utils.print_error(span, msg)

        return m
    else:
        if not utils.args.query_time:
            time_msg = ''
        else:
            time_msg = ' (%s)' % (datetime.now() - start, )
        utils.logger.always_print('ok.%s' % (time_msg,))

        sys.stdout.flush()
        return None


def check_init(s: Solver, safety_only: bool = False) -> Optional[Tuple[syntax.InvariantDecl, Trace]]:
    utils.logger.always_print('checking init:')

    prog = syntax.the_program
    t = s.get_translator((KEY_ONE,))

    with s.new_frame():
        for init in prog.inits():
            s.add(t.translate_expr(init.expr))

        for inv in (prog.invs() if not safety_only else prog.safeties()):
            with s.new_frame():
                s.add(z3.Not(t.translate_expr(inv.expr)))

                if inv.name is not None:
                    msg = ' ' + inv.name
                elif inv.span is not None:
                    msg = ' on line %d' % inv.span[0].lineno
                else:
                    msg = ''
                utils.logger.always_print('  implies invariant%s... ' % msg, end='')
                sys.stdout.flush()

                res = check_unsat([(inv.span, 'invariant%s may not hold in initial state' % msg)],
                                  s, (KEY_ONE,))
                if res is not None:
                    if utils.args.smoke_test_solver:
                        state = State(res, 0)
                        for ax in prog.axioms():
                            if state.eval(ax.expr) is not True:
                                print('\n\n'.join(str(x) for x in s.debug_recent()))
                                print(res)
                                assert False, f'bad initial counterexample for axiom {ax.expr}'
                        for init in prog.inits():
                            if state.eval(init.expr) is not True:
                                print('\n\n'.join(str(x) for x in s.debug_recent()))
                                print(res)
                                assert False, f'bad initial counterexample for initial condition {init.expr}'
                        if state.eval(inv.expr) is not False:
                            print('\n\n'.join(str(x) for x in s.debug_recent()))
                            print(res)
                            assert False, f'bad initial counterexample for invariant {inv.expr}'

                    return inv, res
    return None

def check_transitions(s: Solver) -> Optional[Tuple[syntax.InvariantDecl, Trace, DefinitionDecl]]:
    t = s.get_translator((KEY_OLD, KEY_NEW))
    prog = syntax.the_program

    with s.new_frame():
        for inv in prog.invs():
            s.add(t.translate_expr(inv.expr))

        for trans in prog.transitions():
            if utils.args.check_transition is not None and \
               trans.name not in utils.args.check_transition:
                continue

            utils.logger.always_print('checking transation %s:' % (trans.name,))

            with s.new_frame():
                s.add(t.translate_transition(trans))
                for inv in prog.invs():
                    if utils.args.check_invariant is not None and \
                       inv.name not in utils.args.check_invariant:
                        continue

                    with s.new_frame():
                        s.add(z3.Not(t.translate_expr(inv.expr, index=1)))

                        if inv.name is not None:
                            msg = ' ' + inv.name
                        elif inv.span is not None:
                            msg = ' on line %d' % inv.span[0].lineno
                        else:
                            msg = ''
                        utils.logger.always_print('  preserves invariant%s... ' % msg, end='')
                        sys.stdout.flush()

                        res = check_unsat([(inv.span, 'invariant%s may not be preserved by transition %s'
                                            % (msg, trans.name)),
                                           (trans.span, 'this transition may not preserve invariant%s'
                                            % (msg,))],
                                          s, (KEY_OLD, KEY_NEW))
                        if res is not None:
                            if utils.args.smoke_test_solver:
                                pre_state = res.as_state(i=0)
                                for ax in prog.axioms():
                                    if pre_state.eval(ax.expr) is not True:
                                        print('\n\n'.join(str(x) for x in s.debug_recent()))
                                        print(res)
                                        assert False, f'bad transition counterexample for axiom {ax.expr} in pre state'
                                for pre_inv in prog.invs():
                                    if pre_state.eval(pre_inv.expr) is not True:
                                        print('\n\n'.join(str(x) for x in s.debug_recent()))
                                        print(res)
                                        msg = f'bad transition counterexample for invariant {pre_inv.expr} in pre state'
                                        assert False, msg
                                # need to implement mypyvy-level transition->expression translation
                                # res.eval_double_vocabulary(transition, start_location=0)
                                post_state = res.as_state(i=1)
                                if post_state.eval(inv.expr) is not False:
                                    print('\n\n'.join(str(x) for x in s.debug_recent()))
                                    print(res)
                                    msg = f'bad transition counterexample for invariant {inv.expr} in post state'
                                    assert False, msg

                            return inv, res, trans
    return None

def check_implication(
        s: Solver,
        hyps: Iterable[Expr],
        concs: Iterable[Expr],
        minimize: Optional[bool] = None
) -> Optional[z3.ModelRef]:
    t = s.get_translator((KEY_ONE,))
    with s.new_frame():
        for e in hyps:
            s.add(t.translate_expr(e))
        for e in concs:
            with s.new_frame():
                s.add(z3.Not(t.translate_expr(e)))
                if s.check() != z3.unsat:
                    return s.model(minimize=minimize)

    return None

def check_two_state_implication_all_transitions(
        s: Solver,
        old_hyps: Iterable[Expr],
        new_conc: Expr,
        minimize: Optional[bool] = None,
) -> Optional[Tuple[z3.ModelRef, DefinitionDecl]]:
    t = s.get_translator((KEY_OLD, KEY_NEW))
    prog = syntax.the_program
    with s.new_frame():
        for h in old_hyps:
            s.add(t.translate_expr(h))
        s.add(z3.Not(t.translate_expr(new_conc, index=1)))
        for trans in prog.transitions():
            with s.new_frame():
                s.add(t.translate_transition(trans))
                res = s.check()
                assert res in (z3.sat, z3.unsat), res
                if res != z3.unsat:
                    return s.model(minimize=minimize), trans
        return None

def get_transition_indicator(uid: str, name: str) -> str:
    return '%s_%s_%s' % (TRANSITION_INDICATOR, uid, name)

def assert_any_transition(s: Solver, t: syntax.Z3Translator,
                          key_index: int, allow_stutter: bool = False) -> None:
    prog = syntax.the_program
    uid = str(key_index)

    tids = []
    for transition in prog.transitions():
        tid = z3.Bool(get_transition_indicator(uid, transition.name))
        tids.append(tid)
        s.add(z3.Implies(tid, t.translate_transition(transition, index=key_index)))

    if allow_stutter:
        tid = z3.Bool(get_transition_indicator(uid, '$stutter'))
        tids.append(tid)
        s.add(z3.Implies(tid, z3.And(*t.frame([], index=key_index))))

    s.add(z3.Or(*tids))

class BoundedReachabilityCheck(object):
    def __init__(self, s: Solver, prog: Program,
                 depth: int,
                 preconds: Optional[Iterable[Expr]] = None) -> None:
        self._s = s
        self._prog = prog
        self._depth = depth
        self._preconds = preconds

        self._keys = tuple('state%02d' % i for i in range(depth + 1))
        self._t = self._s.get_translator(self._keys)

    def __enter__(self) -> BoundedReachabilityCheck:
        self._s.push()

        self._add_unrolling_to_solver(self._prog, self._depth, self._preconds)

        return self

    def __exit__(self,
                 exc_type: Optional[typing.Type[BaseException]],
                 exc_value: Optional[BaseException],
                 traceback: Optional[TracebackType]) -> Optional[bool]:
        self._s.pop()
        return None

    def _add_unrolling_to_solver(self, prog: Program,
                                 depth: int,
                                 preconds: Optional[Iterable[Expr]] = None) -> None:
        if preconds is None:
            preconds = (init.expr for init in prog.inits())

        for precond in preconds:
            self._s.add(self._t.translate_expr(precond, index=0))

        for i in range(depth):
            assert_any_transition(self._s, self._t, i, allow_stutter=True)

    def check(self, target: Diagram) -> Optional[Trace]:
        # TODO: important not to use target.to_z3() here (tracking API)
        res = self._s.check([self._t.translate_expr(target.to_ast(), index=len(self._keys) - 1)])
        if res == z3.sat:
            m = Trace.from_z3(tuple(self._keys), self._s.model())
            return m
        elif res == z3.unknown:
            utils.logger.always_print('unknown!')
            utils.logger.always_print('reason unknown: ' + self._s.reason_unknown())
            assert False, 'unexpected unknown from z3!'
        return None

    def check_and_core(self, target: Diagram) -> MySet[int]:
        core: MySet[int] = MySet()

        with self._s.new_frame():
            self._s.add(target.to_z3(self._t, state_index=len(self._keys) - 1))
            res = self._s.check(target.trackers)
            assert res == z3.unsat
            uc = self._s.unsat_core()
            assert uc
        for x in sorted(uc, key=lambda y: y.decl().name()):
            assert isinstance(x, z3.ExprRef)
            core.add(int(x.decl().name()[1:]))

        return core


def check_bmc(s: Solver, safety: Expr, depth: int, preconds: Optional[Iterable[Expr]] = None) -> Optional[Trace]:
    keys = tuple('state%02d' % i for i in range(depth + 1))
    prog = syntax.the_program

    if preconds is None:
        preconds = (init.expr for init in prog.inits())

    t = s.get_translator(keys)

    with s.new_frame():
        for precond in preconds:
            s.add(t.translate_expr(precond, index=0))

        s.add(t.translate_expr(syntax.Not(safety), index=len(keys) - 1))

        for i in range(depth):
            if i != len(keys) - 1:
                s.add(t.translate_expr(safety, index=i))
            assert_any_transition(s, t, i, allow_stutter=False)

        res = s.check()
        if res == z3.sat:
            m = Trace.from_z3(tuple(keys), s.model())
            return m
        elif res == z3.unknown:
            print('unknown!')
        return None


CVC4EXEC = str(utils.PROJECT_ROOT / 'script' / 'run_cvc4.sh')

def cvc4_preprocess(z3str: str) -> str:
    lines = ['(set-logic UF)']
    for st in z3str.splitlines():
        st = st.strip()
        if st == '' or st.startswith(';') or st.startswith('(set-info '):
            continue
        st = st.replace('member', 'member2')
        assert '@' not in st, st
        if st.startswith('(declare-sort ') and not st.endswith(' 0)'):
            assert st.endswith(')'), st
            st = st[:-1] + ' 0)'
        lines.append(st)
    return '\n'.join(lines)

def cvc4_postprocess(cvc4line: str) -> str:
    return cvc4line.replace('member2', 'member')

# The following classes whose names start with 'CVC4' impersonate various classes from z3 in a
# duck typing style. Sometimes, they are given intentionally false type annotations to match
# the corresponding z3 function. Reader beware!!

@dataclass
class CVC4Sort(object):
    name: str

    def __str__(self) -> str:
        return self.name

@dataclass
class CVC4UniverseElement(object):
    name: str
    sort: CVC4Sort

    def __str__(self) -> str:
        return self.name

    def decl(self) -> CVC4UniverseElementDecl:
        return CVC4UniverseElementDecl(self)

@dataclass
class CVC4UniverseElementDecl(object):
    elt: CVC4UniverseElement

    def name(self) -> str:
        return self.elt.name

@dataclass
class CVC4AppExpr(object):
    func: CVC4FuncDecl
    args: List[CVC4UniverseElement]

@dataclass
class CVC4VarDecl(object):
    name: str
    sort: CVC4Sort

@dataclass
class CVC4FuncDecl(object):
    name: str
    var_decls: dataclasses.InitVar[sexp.SList]
    return_sort: str
    body: sexp.Sexp

    def __post_init__(self, var_decls: sexp.SList) -> None:
        self.var_decls: List[CVC4VarDecl] = []
        for d in var_decls:
            assert isinstance(d, sexp.SList), d
            assert len(d) == 2
            var_name, var_sort = d
            assert isinstance(var_name, str), var_name
            assert isinstance(var_sort, str), var_sort
            self.var_decls.append(CVC4VarDecl(var_name, CVC4Sort(var_sort)))

    def __str__(self) -> str:
        return self.name

    def arity(self) -> int:
        return len(self.var_decls)

    def domain(self, i: int) -> z3.SortRef:
        assert i < self.arity(), (i, self.arity())
        return cast(z3.SortRef, self.var_decls[i].sort)

    def __call__(self, *args: z3.ExprRef) -> z3.ExprRef:
        return cast(z3.ExprRef, CVC4AppExpr(self, cast(List[CVC4UniverseElement], list(args))))

@dataclass
class CVC4Model(object):
    sexpr: dataclasses.InitVar[sexp.Sexp]

    def __post_init__(self, sexpr: sexp.Sexp) -> None:
        assert isinstance(sexpr, sexp.SList), sexpr
        self.sexprs = sexpr.contents[1:]

    def sorts(self) -> List[z3.SortRef]:
        ans: List[z3.SortRef] = []
        for s in self.sexprs:
            if isinstance(s, sexp.SList) and s.contents[0] == 'declare-sort':
                name = s.contents[1]
                assert isinstance(name, str), name
                ans.append(cast(z3.SortRef, CVC4Sort(name)))
        return ans

    def eval_in_scope(self, scope: Dict[str, CVC4UniverseElement], e: sexp.Sexp) -> Union[bool, CVC4UniverseElement]:
        # print(scope)
        # print(e)

        if isinstance(e, sexp.SList):
            assert len(e) > 0, e
            f = e[0]
            assert isinstance(f, str), f
            args = e[1:]
            arg_vals = [self.eval_in_scope(scope, arg) for arg in args]
            # print(f)
            # print(arg_vals)
            if f == '=':
                assert len(arg_vals) == 2, arg_vals
                return arg_vals[0] == arg_vals[1]
            elif f == 'and':
                for arg in arg_vals:
                    assert arg is True or arg is False, arg
                return all(arg_vals)
            elif f == 'or':
                for arg in arg_vals:
                    assert arg is True or arg is False, arg
                return any(arg_vals)
            elif f == 'not':
                assert len(arg_vals) == 1
                val = arg_vals[0]
                assert isinstance(val, bool), val
                return not val
            elif f == 'ite':
                assert len(arg_vals) == 3, arg_vals
                branch = arg_vals[0]
                assert isinstance(branch, bool), branch
                if branch:
                    return arg_vals[1]
                else:
                    return arg_vals[2]
            else:
                assert False, ('unsupported function or special form in cvc4 model evaluator', f)
        elif isinstance(e, str):
            if e == 'true':
                return True
            elif e == 'false':
                return False
            else:
                assert e in scope, ('unrecognized variable or symbol in cvc4 model evaluator', e)
                return scope[e]
        else:
            assert False, e

    def eval(self, e: z3.ExprRef, model_completion: bool = False) -> z3.ExprRef:
        cvc4e = cast(Union[CVC4AppExpr], e)
        if isinstance(cvc4e, CVC4AppExpr):
            f = cvc4e.func
            args = cvc4e.args
            scope: Dict[str, CVC4UniverseElement] = {}
            for sort in self.sorts():
                univ = self.get_universe(sort)
                for x in univ:
                    assert isinstance(x, CVC4UniverseElement), x
                    scope[x.name] = x
            for var_decl, value in zip(f.var_decls, args):
                scope[var_decl.name] = value
            ans = self.eval_in_scope(scope, f.body)
            return cast(z3.ExprRef, ans)
        else:
            assert False, ('unsupported expression passed to cvc4 model evaluator', cvc4e)

    def get_universe(self, z3s: z3.SortRef) -> Sequence[z3.ExprRef]:
        sort = cast(CVC4Sort, z3s)
        assert isinstance(sort, CVC4Sort), sort
        for i, sexpr in enumerate(self.sexprs):
            if isinstance(sexpr, sexp.SList) and sexpr.contents[0] == 'declare-sort' and sexpr.contents[1] == sort.name:
                univ: List[z3.ExprRef] = []
                for sexpr in self.sexprs[i + 1:]:
                    prefix = 'rep: '
                    if isinstance(sexpr, sexp.Comment) and sexpr.contents.strip().startswith(prefix):
                        elt_name = sexpr.contents.strip()[len(prefix):]
                        # print(elt_name, sort)
                        univ.append(cast(z3.ExprRef, CVC4UniverseElement(elt_name, sort)))
                    else:
                        break

                return univ
        assert False, ('could not find sort declaration in model', sort)

    def decls(self) -> List[z3.FuncDeclRef]:
        ans: List[z3.FuncDeclRef] = []
        for sexpr in self.sexprs:
            if isinstance(sexpr, sexp.SList) and sexpr.contents[0] == 'define-fun':
                assert len(sexpr.contents) == 5, sexpr
                fun_name = sexpr.contents[1]
                assert isinstance(fun_name, str), fun_name
                args = sexpr.contents[2]
                assert isinstance(args, sexp.SList), args
                return_sort = sexpr.contents[3]
                assert isinstance(return_sort, str), return_sort
                cvc4func = CVC4FuncDecl(fun_name, args, return_sort, sexpr.contents[4])
                # print(cvc4func)
                ans.append(cast(z3.FuncDeclRef, cvc4func))

        return ans

class Solver(object):
    def __init__(self, include_program: bool = True, use_cvc4: bool = False) -> None:
        self.z3solver = z3.Solver()
        prog = syntax.the_program
        assert prog.scope is not None
        assert len(prog.scope.stack) == 0
        self.scope = cast(Scope[z3.ExprRef], prog.scope)
        self.translators: Dict[Tuple[str, ...], syntax.Z3Translator] = {}
        self.nqueries = 0
        self.assumptions_necessary = False
        self.known_keys: Set[str] = set()
        self.mutable_axioms: List[Expr] = []
        self.stack: List[List[z3.ExprRef]] = [[]]
        self.include_program = include_program
        self.use_cvc4 = use_cvc4
        self.cvc4_proc: Optional[subprocess.Popen] = None
        self.cvc4_last_query: Optional[str] = None
        self.cvc4_last_model_response: Optional[str] = None

        if include_program:
            self.register_mutable_axioms(r.derived_axiom for r in prog.derived_relations()
                                         if r.derived_axiom is not None)
            t = self.get_translator()
            for a in prog.axioms():
                self.add(t.translate_expr(a.expr))

    def get_cvc4_proc(self) -> subprocess.Popen:
        if self.cvc4_proc is None:
            self.cvc4_proc = subprocess.Popen([CVC4EXEC], bufsize=1, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                              stderr=subprocess.PIPE, text=True)
        return self.cvc4_proc

    def debug_recent(self) -> Tuple[str, Optional[str], Optional[str]]:
        return (self.z3solver.to_smt2(), self.cvc4_last_query, self.cvc4_last_model_response)

    def restart(self) -> None:
        print('z3solver restart!')
        self.z3solver = z3.Solver()
        for i, frame in enumerate(self.stack):
            if i > 0:
                self.z3solver.push()
            for e in frame:
                self.z3solver.add(e)

    def register_mutable_axioms(self, axioms: Iterable[Expr]) -> None:
        assert self.include_program
        assert len(self.known_keys) == 0, \
            "mutable axioms must be registered before any keys are known to the solver!"
        self.mutable_axioms.extend(axioms)

    def _initialize_key(self, key: Optional[str]) -> None:
        assert self.include_program
        if key is not None and key not in self.known_keys:
            self.known_keys.add(key)

            assert self.z3solver.num_scopes() == 0, \
                "the first time get_translator is called with a particular key, " + \
                "there must be no scopes pushed on the Z3 stack!"

            t = self.get_translator((key,))
            for a in self.mutable_axioms:
                self.add(t.translate_expr(a))

    def get_translator(self, keys: Tuple[str, ...] = ()) -> syntax.Z3Translator:
        assert self.include_program
        t = tuple(keys)
        if t not in self.translators:
            for k in keys:
                self._initialize_key(k)
            self.translators[t] = syntax.Z3Translator(self.scope, keys)
        return self.translators[t]

    @contextmanager
    def mark_assumptions_necessary(self) -> Iterator[None]:
        old = self.assumptions_necessary
        self.assumptions_necessary = True
        yield None
        self.assumptions_necessary = old

    def push(self) -> None:
        self.stack.append([])
        self.z3solver.push()

    def pop(self) -> None:
        self.stack.pop()
        self.z3solver.pop()

    @contextmanager
    def new_frame(self) -> Iterator[None]:
        self.push()
        yield None
        self.pop()

    def add(self, e: z3.ExprRef) -> None:
        # if logger.isEnabledFor(logging.DEBUG):
        #     logger.debug('adding %s' % e)

        self.stack[-1].append(e)
        self.z3solver.add(e)

    def check(self, assumptions: Optional[Sequence[z3.ExprRef]] = None) -> z3.CheckSatResult:
        # logger.debug('solver.check')
        if assumptions is None:
            assert not self.assumptions_necessary
            assumptions = []
        self.nqueries += 1

        if self.use_cvc4:
            cvc4script = cvc4_preprocess(self.z3solver.to_smt2())
            self.cvc4_last_query = cvc4script
            proc = self.get_cvc4_proc()
            print('(reset)', file=proc.stdin)
            print(cvc4script, file=proc.stdin)
            # print(cvc4script)
            assert proc.stdout is not None
            ans = proc.stdout.readline()
            if not ans:
                print(cvc4script)
                out, err = proc.communicate()
                print(out)
                print(err)
                assert False, 'cvc4 closed its stdout before we could get an answer'
            assert ans[-1] == '\n', repr(ans)
            ans = ans.strip()
            ans_map = {
                'sat': z3.sat,
                'unsat': z3.unsat
            }
            assert ans in ans_map, repr(ans)
            return ans_map[ans]

        def luby() -> Iterable[int]:
            l: List[int] = [1]
            k = 1
            i = 0
            while True:
                while i < len(l):
                    yield l[i]
                    i += 1
                l.extend(l)
                l.append(2 ** k)
                k += 1

        if 'restarts' not in utils.args or not utils.args.restarts:
            res = self.z3solver.check(*assumptions)
            if res == z3.unknown:
                print(f'[{datetime.now()}] Solver.check: encountered unknown, printing debug information')
                print(f'[{datetime.now()}] Solver.check: self.assertions:')
                for e in self.assertions():
                    print(e)
                print(f'[{datetime.now()}] Solver.check: assumptions:')
                for e in assumptions:
                    print(e)
                print(f'[{datetime.now()}] Solver.check: self.z3solver stats:')
                print(self.z3solver.statistics())
                print(f'[{datetime.now()}] Solver.check: self.z3solver to_smt2:')
                print(self.z3solver.to_smt2())

                print(f'[{datetime.now()}] Solver.check: trying fresh solver')
                s2 = z3.Solver()
                lator = self.get_translator()
                for a in syntax.the_program.axioms():
                    s2.add(lator.translate_expr(a.expr))
                for e in self.assertions():
                    s2.add(e)

                print(f'[{datetime.now()}] Solver.check: s2.check()', s2.check(*assumptions))
                print(f'[{datetime.now()}] Solver.check: s2 stats:')
                print(s2.statistics())
                print(s2.to_smt2())

                print(f'[{datetime.now()}] Solver.check: trying fresh context')
                ctx = z3.Context()
                s3 = z3.Solver(ctx=ctx)
                for a in syntax.the_program.axioms():
                    s3.add(lator.translate_expr(a.expr).translate(ctx))
                for e in self.assertions():
                    s3.add(e.translate(ctx))

                print(f'[{datetime.now()}] Solver.check: s3.check()',
                      s3.check(*(e.translate(ctx) for e in assumptions)))
                print(f'[{datetime.now()}] Solver.check: s3 stats:')
                print(s3.statistics())
                print(s3.to_smt2())

            assert res in (z3.sat, z3.unsat), (res, self.z3solver.reason_unknown()
                                               if res == z3.unknown else None)
            return res

        unit = 600000
        num_restarts = 0
        max_restarts = 10000
        for t in luby():
            assert num_restarts <= max_restarts, 'exhausted restart budget. exiting.'
            tmt = t * unit
            self.z3solver.set('timeout', tmt)
            t_start = time.time()
            ans = self.z3solver.check(*assumptions)
            if ans != z3.unknown:
                assert ans in (z3.sat, z3.unsat)
                if num_restarts > 0:
                    print(f'z3solver successful after {1000*(time.time() - t_start):.1f}ms: {ans}')
                return ans
            print(f'z3solver returned {ans} after {1000*(time.time() - t_start):.1f}ms '
                  f'(timeout was {tmt}ms), trying again')
            num_restarts += 1
            self.restart()

        assert False

    def _solver_model(self) -> z3.ModelRef:
        if self.use_cvc4:
            proc = self.get_cvc4_proc()
            assert proc.stdout is not None
            print('(get-model)', file=proc.stdin)
            parser = sexp.get_parser('')
            lines = []
            for s in parser.parse():
                if isinstance(s, sexp.EOF):
                    # print('got intermediate EOF')
                    line = cvc4_postprocess(proc.stdout.readline())
                    lines.append(line)
                    if line == '':
                        assert False, 'unexpected underlying EOF'
                    else:
                        line = line.strip()
                        # print(f'got new data line: {line}')
                        parser.add_input(line)
                else:
                    self.cvc4_last_model_response = ''.join(lines)
                    # print('got s-expression. not looking for any more input.')
                    assert isinstance(s, sexp.SList), s
                    # for sub in s:
                    #     print(sub, end='' if isinstance(sub, sexp.Comment) else '\n')
                    return cast(z3.ModelRef, CVC4Model(s))
            else:
                assert False
        else:
            return self.z3solver.model()

    def model(
            self,
            assumptions: Optional[Sequence[z3.ExprRef]] = None,
            minimize: Optional[bool] = None,
            sorts_to_minimize: Optional[Iterable[z3.SortRef]] = None,
            relations_to_minimize: Optional[Iterable[z3.FuncDeclRef]] = None,
    ) -> z3.ModelRef:
        if minimize is None:
            minimize = utils.args.minimize_models
        if minimize:
            if sorts_to_minimize is None:
                sorts_to_minimize = [s.to_z3() for s in self.scope.sorts.values()
                                     if not syntax.has_annotation(s, 'no_minimize')]
            if relations_to_minimize is None:
                m = self._solver_model()
                ds = {str(d) for d in m.decls()}
                rels_to_minimize = []
                for r in self.scope.relations.values():
                    if r.is_derived() or syntax.has_annotation(r, 'no_minimize'):
                        continue
                    if not r.mutable:
                        z3r = r.to_z3(None)
                        if isinstance(z3r, z3.ExprRef):
                            rels_to_minimize.append(z3r.decl())
                        else:
                            rels_to_minimize.append(z3r)
                    else:
                        for k in self.known_keys:
                            z3r = r.to_z3(k)
                            if isinstance(z3r, z3.ExprRef):
                                z3r = z3r.decl()
                            if str(z3r) in ds:
                                rels_to_minimize.append(z3r)

            return self._minimal_model(assumptions, sorts_to_minimize, rels_to_minimize)
        else:
            return self._solver_model()

    def _cardinality_constraint(self, x: Union[z3.SortRef, z3.FuncDeclRef], n: int) -> z3.ExprRef:
        if isinstance(x, z3.SortRef):
            return self._sort_cardinality_constraint(x, n)
        else:
            return self._relational_cardinality_constraint(x, n)

    def _sort_cardinality_constraint(self, s: z3.SortRef, n: int) -> z3.ExprRef:
        x = z3.Const('x$', s)
        disjs = []
        for i in range(n):
            c = z3.Const(f'card$_{s.name()}_{i}', s)
            disjs.append(x == c)

        return z3.Forall(x, z3.Or(*disjs))

    def _relational_cardinality_constraint(self, relation: z3.FuncDeclRef, n: int) -> z3.ExprRef:
        if relation.arity() == 0:
            return z3.BoolVal(True)

        consts = [[z3.Const(f'card$_{relation}_{i}_{j}', relation.domain(j))
                   for j in range(relation.arity())]
                  for i in range(n)]

        vs = [z3.Const(f'x$_{relation}_{j}', relation.domain(j)) for j in range(relation.arity())]

        result = z3.Forall(vs, z3.Implies(relation(*vs), z3.Or(*(
            z3.And(*(
                c == v for c, v in zip(cs, vs)
            ))
            for cs in consts
        ))))
        return result

    def _minimal_model(
            self,
            assumptions: Optional[Sequence[z3.ExprRef]],
            sorts_to_minimize: Iterable[z3.SortRef],
            relations_to_minimize: Iterable[z3.FuncDeclRef],
    ) -> z3.ModelRef:
        with self.new_frame():
            for x in itertools.chain(
                    cast(Iterable[Union[z3.SortRef, z3.FuncDeclRef]], sorts_to_minimize),
                    relations_to_minimize):
                for n in itertools.count(1):
                    with self.new_frame():
                        self.add(self._cardinality_constraint(x, n))
                        res = self.check(assumptions)
                        if res == z3.sat:
                            break
                self.add(self._cardinality_constraint(x, n))

            assert self.check(assumptions) == z3.sat
            return self._solver_model()

    def assertions(self) -> Sequence[z3.ExprRef]:
        asserts = self.z3solver.assertions()
        return sorted(asserts, key=lambda x: str(x))

    def unsat_core(self) -> Sequence[z3.ExprRef]:
        return self.z3solver.unsat_core()

    def reason_unknown(self) -> str:
        return self.z3solver.reason_unknown()

_RelevantDecl = Union[SortDecl, RelationDecl, ConstantDecl, FunctionDecl]

class Diagram(object):
    # This class represents a formula of the form
    #
    #     exists X1, ..., X_k.
    #         C1 & C2 & ... & C_n
    #
    # in a way that is slightly more convenient than a usual ast for computing an
    # unsat core of the C_i.  Instead of just an ast, this class stores a list of
    # vars and a list of conjuncts.  In order to make resolution work seamlessly,
    # it also constructs an internal ast of the formula, which structurally shares
    # all the conjuncts from the list.  This ast is ignored except for purposes
    # of resolving all the C_i.

    def __init__(
            self,
            vs: List[syntax.SortedVar],
            ineqs: Dict[SortDecl, List[Expr]],
            rels: Dict[RelationDecl, List[Expr]],
            consts: Dict[ConstantDecl, Expr],
            funcs: Dict[FunctionDecl, List[Expr]]
    ) -> None:
        self.binder = syntax.Binder(vs)
        self.ineqs = ineqs
        self.rels = rels
        self.consts = consts
        self.funcs = funcs
        self.trackers: List[z3.ExprRef] = []
        self.tombstones: Dict[_RelevantDecl, Optional[Set[int]]] = defaultdict(set)

    def ineq_conjuncts(self) -> Iterable[Tuple[SortDecl, int, Expr]]:
        for s, l in self.ineqs.items():
            S = self.tombstones[s]
            if S is not None:
                for i, e in enumerate(l):
                    if i not in S:
                        yield s, i, e

    def rel_conjuncts(self) -> Iterable[Tuple[RelationDecl, int, Expr]]:
        for r, l in self.rels.items():
            S = self.tombstones[r]
            if S is not None:
                for i, e in enumerate(l):
                    if i not in S:
                        yield r, i, e

    def func_conjuncts(self) -> Iterable[Tuple[FunctionDecl, int, Expr]]:
        for f, l in self.funcs.items():
            S = self.tombstones[f]
            if S is not None:
                for i, e in enumerate(l):
                    if i not in S:
                        yield f, i, e

    def const_conjuncts(self) -> Iterable[Tuple[ConstantDecl, int, Expr]]:
        for c, e in self.consts.items():
            S = self.tombstones[c]
            if S is not None and 0 not in S:
                yield c, 0, e

    def const_subst(self) -> Dict[syntax.Id, syntax.Id]:
        ans = {}
        for c, e in self.consts.items():
            assert isinstance(e, syntax.BinaryExpr) and e.op == 'EQUAL' and \
                isinstance(e.arg1, syntax.Id) and isinstance(e.arg2, syntax.Id)
            ans[e.arg2] = e.arg1
        return ans

    def conjuncts(self) -> Iterable[Tuple[_RelevantDecl, int, Expr]]:
        for t1 in self.ineq_conjuncts():
            yield t1
        for t2 in self.rel_conjuncts():
            yield t2
        for t3 in self.const_conjuncts():
            yield t3
        for t4 in self.func_conjuncts():
            yield t4

    def simplify_consts(self) -> None:
        subst = self.const_subst()
        I: Dict[SortDecl, List[Expr]]
        R: Dict[RelationDecl, List[Expr]]
        C: Dict[ConstantDecl, Expr]
        F: Dict[FunctionDecl, List[Expr]]

        def apply_subst1(e: Expr) -> Expr:
            return syntax.subst_vars_simple(e, subst)

        def apply_subst(l: List[Expr]) -> List[Expr]:
            return [apply_subst1(e) for e in l]

        def is_trivial_eq(eq: Expr) -> bool:
            return isinstance(eq, syntax.BinaryExpr) and eq.op == 'EQUAL' and \
                eq.arg1 == eq.arg2

        I = OrderedDict((s, apply_subst(l)) for s, l in self.ineqs.items())
        R = OrderedDict((r, apply_subst(l)) for r, l in self.rels.items())
        C = OrderedDict((c, apply_subst1(e)) for c, e in self.consts.items())
        F = OrderedDict((f, apply_subst(l)) for f, l in self.funcs.items())

        self.ineqs = I
        self.rels = R
        self.consts = OrderedDict((c, e) for c, e in C.items() if not is_trivial_eq(e))
        self.funcs = F

        self.prune_unused_vars()

    def __str__(self) -> str:
        return 'exists %s.\n  %s' % (
            ', '.join(v.name for v in self.binder.vs),
            ' &\n  '.join(str(c) for _, _, c in self.conjuncts())
        )

    def resolve(self, scope: Scope) -> None:
        self.binder.pre_resolve(scope)

        with scope.in_scope(self.binder, [v.sort for v in self.binder.vs]):
            with scope.n_states(1):
                for _, _, c in self.conjuncts():
                    c.resolve(scope, syntax.BoolSort)

        self.binder.post_resolve()

    def vs(self) -> List[syntax.SortedVar]:
        return self.binder.vs

    def to_z3(self, t: syntax.Z3Translator, state_index: int = 0) -> z3.ExprRef:
        bs = t.bind(self.binder)
        with t.scope.in_scope(self.binder, bs):
            z3conjs = []
            self.trackers = []
            self.reverse_map: List[Tuple[_RelevantDecl, int]] = []
            i = 0

            for (d, j, c) in self.conjuncts():
                p = z3.Bool('p%d' % i)
                self.trackers.append(p)
                self.reverse_map.append((d, j))
                z3conjs.append(p == t.translate_expr(c, index=state_index))
                i += 1

        if bs:
            return z3.Exists(bs, z3.And(*z3conjs))
        else:
            return z3.And(*z3conjs)

    def to_ast(self) -> Expr:
        e = syntax.And(*(c for _, _, c in self.conjuncts()))
        vs = self.binder.vs

        return syntax.Exists(vs, e)

    # TODO: can be removed? replaced with Frames.valid_in_initial_frame (YF)
    def valid_in_init(self, s: Solver, minimize: Optional[bool] = None) -> bool:
        prog = syntax.the_program
        return check_implication(s, (init.expr for init in prog.inits()),
                                 [syntax.Not(self.to_ast())], minimize=minimize) is None

    def minimize_from_core(self, core: Optional[Iterable[int]]) -> None:
        if core is None:
            return

        I: Dict[SortDecl, List[Expr]] = {}
        R: Dict[RelationDecl, List[Expr]] = {}
        C: Dict[ConstantDecl, Expr] = {}
        F: Dict[FunctionDecl, List[Expr]] = {}

        for i in core:
            d, j = self.reverse_map[i]
            if isinstance(d, SortDecl):
                if d not in I:
                    I[d] = []
                I[d].append(self.ineqs[d][j])
            elif isinstance(d, RelationDecl):
                if d not in R:
                    R[d] = []
                R[d].append(self.rels[d][j])
            elif isinstance(d, FunctionDecl):
                if d not in F:
                    F[d] = []
                F[d].append(self.funcs[d][j])

            else:
                assert isinstance(d, ConstantDecl)
                assert d not in C
                C[d] = self.consts[d]

        self.prune_unused_vars()

        self.ineqs = I
        self.rels = R
        self.consts = C
        self.funcs = F

    def remove_clause(self, d: _RelevantDecl, i: Union[int, Set[int], None] = None) -> None:
        if i is None:
            self.tombstones[d] = None
        elif isinstance(i, int):
            S = self.tombstones[d]
            assert S is not None
            assert i not in S
            S.add(i)
        else:
            S = self.tombstones[d]
            assert S is not None
            assert i & S == set()
            S |= i

    def prune_unused_vars(self) -> None:
        self.binder.vs = [v for v in self.binder.vs
                          if any(v.name in c.free_ids() for _, _, c in self.conjuncts())]

    @contextmanager
    def without(self, d: _RelevantDecl, j: Union[int, Set[int], None] = None) -> Iterator[None]:
        S = self.tombstones[d]
        if j is None:
            self.tombstones[d] = None
            yield
            self.tombstones[d] = S
        elif isinstance(j, int):
            assert S is not None
            assert j not in S
            S.add(j)
            yield
            S.remove(j)
        else:
            assert S is not None
            assert S & j == set()
            S |= j
            yield
            S -= j

    def generalize(self, s: Solver, constraint: Callable[[Diagram], bool]) -> None:
        'drop conjuncts of this diagram subject to the constraint returning true'
        d: _RelevantDecl
        I: Iterable[_RelevantDecl] = self.ineqs
        R: Iterable[_RelevantDecl] = self.rels
        C: Iterable[_RelevantDecl] = self.consts
        F: Iterable[_RelevantDecl] = self.funcs

        assert constraint(self)

        for d in itertools.chain(I, R, C, F):
            if isinstance(d, SortDecl) and len(self.ineqs[d]) == 1:
                continue
            with self.without(d):
                res = constraint(self)
            if res:
                self.remove_clause(d)
                continue
            if isinstance(d, RelationDecl):
                l = self.rels[d]
                cs = set()
                S = self.tombstones[d]
                assert S is not None
                for j, x in enumerate(l):
                    if j not in S and isinstance(x, syntax.UnaryExpr):
                        cs.add(j)
                with self.without(d, cs):
                    res = constraint(self)
                if res:
                    self.remove_clause(d, cs)

        for d, j, c in self.conjuncts():
            with self.without(d, j):
                res = constraint(self)
            if res:
                self.remove_clause(d, j)

        self.prune_unused_vars()

_digits_re = re.compile(r'(?P<prefix>.*?)(?P<suffix>[0-9]+)$')

def try_printed_by(state: State, s: SortDecl, elt: str) -> Optional[str]:
    custom_printer_annotation = syntax.get_annotation(s, 'printed_by')

    if custom_printer_annotation is not None:
        assert len(custom_printer_annotation.args) >= 1
        import importlib
        printers = importlib.import_module('printers')
        printer_name = custom_printer_annotation.args[0]
        custom_printer = printers.__dict__.get(printer_name)
        custom_printer_args = custom_printer_annotation.args[1:] \
            if custom_printer is not None else []
        if custom_printer is not None:
            return custom_printer(state, s, elt, custom_printer_args)
        else:
            utils.print_warning(custom_printer_annotation.span,
                                'could not find printer named %s' % (printer_name,))
    return None

def print_element(state: State, s: Union[SortDecl, syntax.Sort], elt: str) -> str:
    if not isinstance(s, SortDecl):
        s = syntax.get_decl_from_sort(s)

    return try_printed_by(state, s, elt) or elt

def print_tuple(state: State, arity: List[syntax.Sort], tup: List[str]) -> str:
    l = []
    assert len(arity) == len(tup)
    for s, x in zip(arity, tup):
        l.append(print_element(state, s, x))
    return ','.join(l)

def _univ_str(state: State) -> List[str]:
    l = []
    for s in sorted(state.univs().keys(), key=str):
        if syntax.has_annotation(s, 'no_print'):
            continue

        l.append(str(s))

        def key(x: str) -> Tuple[str, int]:
            ans = print_element(state, s, x)
            if (m := _digits_re.match(ans)) is not None:
                return (m['prefix'], int(m['suffix']))
            else:
                return (ans, 0)
        for x in sorted(state.univs()[s], key=key):
            l.append('  %s' % print_element(state, s, x))
    return l

def _state_str(
        state: State,
) -> str:
    l = []

    Cs = state.const_interp()
    for C in Cs:
        if syntax.has_annotation(C, 'no_print'):
            continue
        l.append('%s = %s' % (C.name, print_element(state, C.sort, Cs[C])))

    Rs = state.rel_interp()
    for R in Rs:
        if syntax.has_annotation(R, 'no_print'):
            continue
        for tup, b in sorted(Rs[R], key=lambda x: print_tuple(state, R.arity, x[0])):
            if b:
                l.append('%s%s(%s)' % ('' if b else '!', R.name,
                                       print_tuple(state, R.arity, tup)))

    Fs = state.func_interp()
    for F in Fs:
        if syntax.has_annotation(F, 'no_print'):
            continue
        for tup, res in sorted(Fs[F], key=lambda x: print_tuple(state, F.arity, x[0])):
            l.append('%s(%s) = %s' % (F.name, print_tuple(state, F.arity, tup),
                                      print_element(state, F.sort, res)))

    return '\n'.join(l)


Universe = Dict[SortDecl, List[str]]
RelationInterp = Dict[RelationDecl, List[Tuple[List[str], bool]]]
ConstantInterp = Dict[ConstantDecl, str]
FunctionInterp = Dict[FunctionDecl, List[Tuple[List[str], str]]]

class Trace(object):
    def __init__(
            self,
            keys: Tuple[str, ...],
    ) -> None:
        self.keys = keys

        self.univs: Universe = OrderedDict()

        self.immut_rel_interps: RelationInterp = OrderedDict()
        self.immut_const_interps: ConstantInterp = OrderedDict()
        self.immut_func_interps: FunctionInterp = OrderedDict()

        self.rel_interps: List[RelationInterp] = [OrderedDict() for i in range(len(self.keys))]
        self.const_interps: List[ConstantInterp] = [OrderedDict() for i in range(len(self.keys))]
        self.func_interps: List[FunctionInterp] = [OrderedDict() for i in range(len(self.keys))]

        self.transitions: List[str] = ['' for i in range(len(self.keys) - 1)]
        self.onestate_formula_cache: Dict[int, Expr] = {}
        self.diagram_cache: Dict[int, Diagram] = {}

    @staticmethod
    def from_z3(keys: Tuple[str, ...], z3m: z3.ModelRef, allow_undefined: bool = False) -> Trace:
        m = Trace(keys)
        m.read_out(z3m, allow_undefined=allow_undefined)
        return m

    # for pickling
    def __getstate__(self) -> Any:
        return dict(
            self.__dict__,
            z3model=None,
        )
    # __setstate__ is not really needed, since the following is the default:
    # def __setstate__(self, state:Any) -> None:
    #     self.__dict__.update(state)

    def __str__(self) -> str:
        l = []
        dummy_state = State(self, None)
        l.extend(_univ_str(dummy_state))
        l.append(_state_str(dummy_state))
        for i, k in enumerate(self.keys):
            if i > 0 and self.transitions[i - 1] != '':
                l.append('\ntransition %s' % (self.transitions[i - 1],))
            l.append('\nstate %s:' % (i,))
            l.append(_state_str(State(self, i)))

        return '\n'.join(l)

    def read_out(self, z3model: z3.ModelRef, allow_undefined: bool = False) -> None:
        def rename(s: str) -> str:
            return s.replace('!val!', '').replace('@uc_', '')

        def _eval(expr: z3.ExprRef) -> z3.ExprRef:
            ans = z3model.eval(expr, model_completion=True)
            assert bool(ans) is True or bool(ans) is False, (expr, ans)
            return ans

        prog = syntax.the_program

        for z3sort in sorted(z3model.sorts(), key=str):
            sort = prog.scope.get_sort(str(z3sort))
            assert sort is not None
            univ = z3model.get_universe(z3sort)
            self.univs[sort] = list(sorted(rename(str(x)) for x in univ))

        model_decls = z3model.decls()
        all_decls = model_decls
        for z3decl in sorted(all_decls, key=str):
            z3name = str(z3decl)
            for i, k in enumerate(self.keys):
                if z3name.startswith(k):
                    name = z3name[len(k + '_'):]
                    R = self.rel_interps[i]
                    C = self.const_interps[i]
                    F = self.func_interps[i]
                    break
            else:
                name = z3name
                R = self.immut_rel_interps
                C = self.immut_const_interps
                F = self.immut_func_interps

            decl = prog.scope.get(name)
            assert not isinstance(decl, syntax.Sort) and \
                not isinstance(decl, syntax.SortInferencePlaceholder)
            if decl is not None:
                if isinstance(decl, RelationDecl):
                    if decl.arity:
                        rl = []
                        domains = [z3model.get_universe(z3decl.domain(i))
                                   for i in range(z3decl.arity())]
                        if not any(x is None for x in domains):
                            # Note: if any domain is None, we silently drop this symbol.
                            # It's not entirely clear that this is an ok thing to do.
                            g = itertools.product(*domains)
                            for row in g:
                                relation_expr = z3decl(*row)
                                ans = _eval(relation_expr)
                                rl.append(([rename(str(col)) for col in row], bool(ans)))
                            assert decl not in R
                            R[decl] = rl
                    else:
                        ans = z3model.eval(z3decl())
                        assert decl not in R
                        R[decl] = [([], bool(ans))]
                elif isinstance(decl, FunctionDecl):
                    fl = []
                    domains = [z3model.get_universe(z3decl.domain(i))
                               for i in range(z3decl.arity())]
                    if not any(x is None for x in domains):
                        # Note: if any domain is None, we silently drop this symbol.
                        # It's not entirely clear that this is an ok thing to do.
                        g = itertools.product(*domains)
                        for row in g:
                            ans = z3model.eval(z3decl(*row))
                            fl.append(([rename(str(col)) for col in row],
                                       rename(ans.decl().name())))
                        assert decl not in F
                        F[decl] = fl

                else:
                    assert isinstance(decl, ConstantDecl)
                    v = z3model.eval(z3decl()).decl().name()
                    assert decl not in C
                    C[decl] = rename(v)
            else:
                if name.startswith(TRANSITION_INDICATOR + '_') and z3model.eval(z3decl()):
                    name = name[len(TRANSITION_INDICATOR + '_'):]
                    istr, name = name.split('_', maxsplit=1)
                    i = int(istr)
                    if i < len(self.transitions):
                        self.transitions[i] = name
                    else:
                        # TODO: not sure what's going on here with check_bmc and pd.check_k_state_implication
                        # assert False
                        pass

        if allow_undefined:
            return

        def get_univ(d: SortDecl) -> List[str]:
            if d not in self.univs:
                self.univs[d] = [d.name + '0']
            return self.univs[d]

        def arbitrary_interp_r(r: RelationDecl) -> List[Tuple[List[str], bool]]:
            doms = [get_univ(syntax.get_decl_from_sort(s)) for s in r.arity]

            l = []
            tup: Tuple[str, ...]
            for tup in itertools.product(*doms):
                l.append((list(tup), False))

            return l

        def ensure_defined_r(r: RelationDecl) -> None:
            R: List[Dict[RelationDecl, List[Tuple[List[str], bool]]]]
            if not r.mutable:
                R = [self.immut_rel_interps]
            else:
                R = self.rel_interps
            interp: Optional[List[Tuple[List[str], bool]]] = None

            def get_interp() -> List[Tuple[List[str], bool]]:
                nonlocal interp
                if interp is None:
                    interp = arbitrary_interp_r(r)
                return interp

            for m in R:
                if r not in m:
                    m[r] = get_interp()

        def arbitrary_interp_c(c: ConstantDecl) -> str:
            sort = c.sort
            return get_univ(syntax.get_decl_from_sort(sort))[0]

        def ensure_defined_c(c: ConstantDecl) -> None:
            R: List[Dict[RelationDecl, List[Tuple[List[str], bool]]]]
            if not c.mutable:
                C = [self.immut_const_interps]
            else:
                C = self.const_interps

            interp: str = arbitrary_interp_c(c)

            for m in C:
                if c not in m:
                    m[c] = interp

        def arbitrary_interp_f(f: FunctionDecl) -> List[Tuple[List[str], str]]:
            doms = [get_univ(syntax.get_decl_from_sort(s)) for s in f.arity]

            interp = get_univ(syntax.get_decl_from_sort(f.sort))[0]

            l = []
            tup: Tuple[str, ...]
            for tup in itertools.product(*doms):
                l.append((list(tup), interp))

            return l

        def ensure_defined_f(f: FunctionDecl) -> None:
            F: List[Dict[FunctionDecl, List[Tuple[List[str], str]]]]
            if not f.mutable:
                F = [self.immut_func_interps]
            else:
                F = self.func_interps

            interp: Optional[List[Tuple[List[str], str]]] = None

            def get_interp() -> List[Tuple[List[str], str]]:
                nonlocal interp
                if interp is None:
                    interp = arbitrary_interp_f(f)
                return interp

            for m in F:
                if f not in m:
                    m[f] = get_interp()

        for decl in prog.relations_constants_and_functions():
            if isinstance(decl, RelationDecl):
                ensure_defined_r(decl)
            elif isinstance(decl, ConstantDecl):
                ensure_defined_c(decl)
            else:
                assert isinstance(decl, FunctionDecl)
                ensure_defined_f(decl)

    def as_diagram(self, index: Optional[int] = None) -> Diagram:
        assert len(self.keys) == 1 or index is not None, \
            'to generate a diagram from a multi-state model, you must specify which state you want'
        assert index is None or (0 <= index and index < len(self.keys))

        if index is None:
            index = 0

        prog = syntax.the_program

        mut_rel_interps = self.rel_interps[index]
        mut_const_interps = self.const_interps[index]
        mut_func_interps = self.func_interps[index]

        vars_by_sort: Dict[SortDecl, List[syntax.SortedVar]] = OrderedDict()
        ineqs: Dict[SortDecl, List[Expr]] = OrderedDict()
        rels: Dict[RelationDecl, List[Expr]] = OrderedDict()
        consts: Dict[ConstantDecl, Expr] = OrderedDict()
        funcs: Dict[FunctionDecl, List[Expr]] = OrderedDict()
        for sort in self.univs:
            vars_by_sort[sort] = [syntax.SortedVar(v, syntax.UninterpretedSort(sort.name))
                                  for v in self.univs[sort]]
            u = [syntax.Id(s) for s in self.univs[sort]]
            ineqs[sort] = [syntax.Neq(a, b) for a, b in itertools.combinations(u, 2)]

        for R, l in itertools.chain(mut_rel_interps.items(), self.immut_rel_interps.items()):
            rels[R] = []
            for tup, ans in l:
                e: Expr
                if tup:
                    args: List[Expr] = []
                    for (col, col_sort) in zip(tup, R.arity):
                        assert isinstance(col_sort, syntax.UninterpretedSort)
                        assert col_sort.decl is not None
                        args.append(syntax.Id(col))
                    e = syntax.AppExpr(R.name, args)
                else:
                    e = syntax.Id(R.name)
                e = e if ans else syntax.Not(e)
                rels[R].append(e)
        for C, c in itertools.chain(mut_const_interps.items(), self.immut_const_interps.items()):
            e = syntax.Eq(syntax.Id(C.name), syntax.Id(c))
            consts[C] = e
        for F, fl in itertools.chain(mut_func_interps.items(), self.immut_func_interps.items()):
            funcs[F] = []
            for tup, res in fl:
                e = syntax.AppExpr(F.name, [syntax.Id(col) for col in tup])
                e = syntax.Eq(e, syntax.Id(res))
                funcs[F].append(e)

        vs = list(itertools.chain(*(vs for vs in vars_by_sort.values())))
        diag = Diagram(vs, ineqs, rels, consts, funcs)
        if utils.args.simplify_diagram:
            diag.simplify_consts()
        assert prog.scope is not None
        diag.resolve(prog.scope)

        return diag

    def as_onestate_formula(self, index: Optional[int] = None) -> Expr:
        assert len(self.keys) == 1 or index is not None, \
            'to generate a onestate formula from a multi-state model, ' + \
            'you must specify which state you want'
        assert index is None or (0 <= index and index < len(self.keys))

        if index is None:
            index = 0

        if index not in self.onestate_formula_cache:
            prog = syntax.the_program

            mut_rel_interps = self.rel_interps[index]
            mut_const_interps = self.const_interps[index]
            mut_func_interps = self.func_interps[index]

            vs: List[syntax.SortedVar] = []
            ineqs: Dict[SortDecl, List[Expr]] = OrderedDict()
            rels: Dict[RelationDecl, List[Expr]] = OrderedDict()
            consts: Dict[ConstantDecl, Expr] = OrderedDict()
            funcs: Dict[FunctionDecl, List[Expr]] = OrderedDict()
            for sort in self.univs:
                vs.extend(syntax.SortedVar(v, syntax.UninterpretedSort(sort.name))
                          for v in self.univs[sort])
                u = [syntax.Id(v) for v in self.univs[sort]]
                ineqs[sort] = [syntax.Neq(a, b) for a, b in itertools.combinations(u, 2)]
            for R, l in itertools.chain(mut_rel_interps.items(), self.immut_rel_interps.items()):
                rels[R] = []
                for tup, ans in l:
                    e = (
                        syntax.AppExpr(R.name, [syntax.Id(col) for col in tup])
                        if tup else syntax.Id(R.name)
                    )
                    rels[R].append(e if ans else syntax.Not(e))
            for C, c in itertools.chain(mut_const_interps.items(), self.immut_const_interps.items()):
                consts[C] = syntax.Eq(syntax.Id(C.name), syntax.Id(c))
            for F, fl in itertools.chain(mut_func_interps.items(), self.immut_func_interps.items()):
                funcs[F] = [
                    syntax.Eq(syntax.AppExpr(F.name, [syntax.Id(col) for col in tup]),
                              syntax.Id(res))
                    for tup, res in fl
                ]

            # get a fresh variable, avoiding names of universe elements in vs
            fresh = prog.scope.fresh('x', [v.name for v in vs])

            e = syntax.Exists(vs, syntax.And(
                *itertools.chain(*ineqs.values(), *rels.values(), consts.values(), *funcs.values(), (
                    syntax.Forall([syntax.SortedVar(fresh,
                                                    syntax.UninterpretedSort(sort.name))],
                                  syntax.Or(*(syntax.Eq(syntax.Id(fresh), syntax.Id(v))
                                              for v in self.univs[sort])))
                    for sort in self.univs
                ))))
            assert prog.scope is not None
            with prog.scope.n_states(1):
                e.resolve(prog.scope, None)
            self.onestate_formula_cache[index] = e
        return self.onestate_formula_cache[index]

    def as_state(self, i: Optional[int]) -> State:
        assert i is None or (0 <= i and i < len(self.keys))
        return State(self, i)

    def eval(self, full_expr: Expr, starting_index: Optional[int]) -> Union[str, bool]:
        def go(expr: Expr, index: Optional[int]) -> Union[str, bool]:
            def current_rels() -> Dict[RelationDecl, List[Tuple[List[str], bool]]]:
                return dict(itertools.chain(self.immut_rel_interps.items(),
                                            self.rel_interps[index].items() if index is not None else []))

            def current_consts() -> Dict[ConstantDecl, str]:
                return dict(itertools.chain(self.immut_const_interps.items(),
                                            self.const_interps[index].items() if index is not None else []))

            def current_funcs() -> Dict[FunctionDecl, List[Tuple[List[str], str]]]:
                return dict(itertools.chain(self.immut_func_interps.items(),
                                            self.func_interps[index].items() if index is not None else []))
            scope: syntax.Scope[Union[str, bool]] = \
                cast(syntax.Scope[Union[str, bool]], syntax.the_program.scope)
            if isinstance(expr, syntax.Bool):
                return expr.val
            elif isinstance(expr, syntax.UnaryExpr):
                if expr.op == 'NEW':
                    assert index is not None
                    return go(expr.arg, index=index + 1)
                elif expr.op == 'NOT':
                    return not go(expr.arg, index)
                assert False, "eval unknown operation %s" % expr.op
            elif isinstance(expr, syntax.BinaryExpr):
                if expr.op == 'IMPLIES':
                    return not go(expr.arg1, index) or go(expr.arg2, index)
                elif expr.op in ['IFF', 'EQUAL']:
                    return go(expr.arg1, index) == go(expr.arg2, index)
                else:
                    assert expr.op == 'NOTEQ'
                    return go(expr.arg1, index) != go(expr.arg2, index)
            elif isinstance(expr, syntax.NaryExpr):
                assert expr.op in ['AND', 'OR', 'DISTINCT']
                if expr.op in ['AND', 'OR']:
                    p = all if expr.op == 'AND' else any
                    return p(go(arg, index) for arg in expr.args)
                else:
                    assert expr.op == 'DISTINCT'
                    return len(set(go(arg, index) for arg in expr.args)) == len(expr.args)
            elif isinstance(expr, syntax.AppExpr):
                d = scope.get(expr.callee)
                assert isinstance(d, syntax.RelationDecl) or isinstance(d, syntax.FunctionDecl)
                table: Sequence[Tuple[Sequence[str], Union[bool, str]]]
                if isinstance(d, syntax.RelationDecl):
                    table = current_rels()[d]
                else:
                    table = current_funcs()[d]
                args = []
                for arg in expr.args:
                    ans = go(arg, index)
                    assert isinstance(ans, str)
                    args.append(ans)
                return _lookup_assoc(table, args)
            elif isinstance(expr, syntax.QuantifierExpr):
                assert expr.quant in ['FORALL', 'EXISTS']
                p = all if expr.quant == 'FORALL' else any
                doms = [self.univs[syntax.get_decl_from_sort(sv.sort)] for sv in expr.binder.vs]

                def one(q: syntax.QuantifierExpr, tup: Tuple[str, ...]) -> bool:
                    with scope.in_scope(q.binder, list(tup)):
                        ans = go(q.body, index)
                        assert isinstance(ans, bool)
                        return ans
                return p(one(expr, t) for t in itertools.product(*doms))
            elif isinstance(expr, syntax.Id):
                a = scope.get(expr.name)
                # definitions are not supported
                assert not isinstance(a, syntax.DefinitionDecl) and \
                    not isinstance(a, syntax.FunctionDecl) and a is not None
                if isinstance(a, syntax.RelationDecl):
                    return _lookup_assoc(current_rels()[a], [])
                elif isinstance(a, syntax.ConstantDecl):
                    return current_consts()[a]
                elif isinstance(a, tuple):
                    # bound variable introduced to scope
                    (bound_elem,) = a
                    return bound_elem
                else:
                    assert isinstance(a, str) or isinstance(a, bool)
                    return a
            elif isinstance(expr, syntax.IfThenElse):
                branch = go(expr.branch, index)
                assert isinstance(branch, bool)
                return go(expr.then, index) if branch else go(expr.els, index)
            elif isinstance(expr, syntax.Let):
                val = go(expr.val, index)
                with scope.in_scope(expr.binder, [val]):
                    return go(expr.body, index)
            else:
                assert False, expr

        return go(full_expr, index=starting_index)

_K = TypeVar('_K')
_V = TypeVar('_V')

def _lookup_assoc(l: Sequence[Tuple[_K, _V]], k: _K) -> _V:
    for k2, v2 in l:
        if k == k2:
            return v2
    assert False

@dataclass
class State:
    trace: Trace
    index: Optional[int]

    def __str__(self) -> str:
        return '\n'.join(_univ_str(self) + [_state_str(self)])

    def eval(self, e: Expr) -> Union[str, bool]:
        return self.trace.eval(e, starting_index=self.index)

    def as_diagram(self) -> Diagram:
        return self.trace.as_diagram(index=self.index)

    def as_onestate_formula(self) -> Expr:
        return self.trace.as_onestate_formula(index=self.index)

    def univs(self) -> Universe:
        return self.trace.univs

    def rel_interp(self) -> RelationInterp:
        if self.index is None:
            return self.trace.immut_rel_interps
        else:
            return self.trace.rel_interps[self.index]

    def const_interp(self) -> ConstantInterp:
        if self.index is None:
            return self.trace.immut_const_interps
        else:
            return self.trace.const_interps[self.index]

    def func_interp(self) -> FunctionInterp:
        if self.index is None:
            return self.trace.immut_func_interps
        else:
            return self.trace.func_interps[self.index]

    def element_sort(self, element_name: str) -> SortDecl:
        matching_sorts = [sort for (sort, univ) in self.univs().items()
                          if element_name in univ]
        assert matching_sorts, "%s unknown element name" % element_name
        assert len(matching_sorts) == 1, "ambiguous element name %s" % element_name
        return matching_sorts[0]
