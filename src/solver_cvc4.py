'''
This module contains everything specific to using CVC4 in mypyvy. (Except for some leftovers still in class Solver.)

Currently, using cvc4 is done by communicating with a subprocess in SMT-LIB2. We generate the smt2 by dumping from z3, and parse the model using sexpr.py.

As of now, the cvc4 process is reset using (reset) before every (check-sat).

Note: cvc4 is guaranteed to return a model of minimal cardinality, so
we don't minimize models.

TODO: respect timeout

'''
from __future__ import annotations
from collections import OrderedDict, defaultdict
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime
import dataclasses
import time
import itertools
import math
import random
import io
import re
import sexp
import subprocess
import sys
from typing import List, Optional, Set, Tuple, Union, Iterable, Dict, Sequence, Iterator
from typing import cast, TypeVar, Callable

import z3

import utils
import typechecker
import syntax
from syntax import Expr, Scope, ConstantDecl, RelationDecl, SortDecl
from syntax import FunctionDecl, DefinitionDecl, Not, New
from semantics import Trace, State, FirstOrderStructure


CVC4EXEC = str(utils.PROJECT_ROOT / 'script' / 'run_cvc4.sh')


def new_cvc4_process() -> subprocess.Popen:
    return subprocess.Popen(
        [CVC4EXEC],
        bufsize=1,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )


_cvc4_last_query: str = ''
_cvc4_last_model_response: str = ''


def check_with_cvc4(cvc4_proc: subprocess.Popen, smt2: str) -> Optional[CVC4Model]:
    global _cvc4_last_query
    global _cvc4_last_model_response
    cvc4script = cvc4_preprocess(smt2)
    _cvc4_last_query = cvc4script
    print('(reset)', file=cvc4_proc.stdin)
    print(cvc4script, file=cvc4_proc.stdin)
    # print(cvc4script)
    assert cvc4_proc.stdout is not None
    ans = cvc4_proc.stdout.readline()
    if not ans:
        print(cvc4script)
        out, err = cvc4_proc.communicate()
        print(out)
        print(err)
        assert False, 'cvc4 closed its stdout before we could get an answer'
    assert ans[-1] == '\n', repr(ans)
    ans = ans.strip()
    if ans == 'unsat':
        return None
    elif ans == 'sat':
        # get model
        print('(get-model)', file=cvc4_proc.stdin)
        parser = sexp.get_parser('')
        lines = []
        for s in parser.parse():
            if isinstance(s, sexp.EOF):
                # print('got intermediate EOF')
                line = cvc4_postprocess(cvc4_proc.stdout.readline())
                lines.append(line)
                if line == '':
                    assert False, 'unexpected underlying EOF'
                else:
                    line = line.strip()
                    # print(f'got new data line: {line}')
                    parser.add_input(line)
            else:
                _cvc4_last_model_response = ''.join(lines)
                # print(f'\n\nQUERY:\n{_cvc4_last_query}\n\n')
                # print(f'\n\nMODEL:\n{_cvc4_last_model_response}\n\n')
                # print('got s-expression. not looking for any more input.')
                assert isinstance(s, sexp.SList), s
                # for sub in s:
                #     print(sub, end='' if isinstance(sub, sexp.Comment) else '\n')
                return CVC4Model(s)
        else:
            assert False
    else:
        assert False, (f'cvc4 returned unexpected answer to (check-sat): {ans!r}'
                       f'\n\nQUERY:\n{_cvc4_last_query}\n\n')


def cvc4_preprocess(z3str: str) -> str:
    lines = ['(set-logic UFNIA)']
    for st in z3str.splitlines():
        st = st.strip()
        if st == '' or st.startswith(';') or st.startswith('(set-info '):
            continue
        # st = st.replace('member', 'member2')
        assert '@' not in st, st
        if st.startswith('(declare-sort ') and not st.endswith(' 0)'):
            assert False, st
            assert st.endswith(')'), st
            st = st[:-1] + ' 0)'
        lines.append(st)
    return '\n'.join(lines)

def cvc4_postprocess(cvc4line: str) -> str:
    return cvc4line
    # return cvc4line.replace('member2', 'member')

# The following classes whose names start with 'CVC4' impersonate various classes from z3 in a
# duck typing style. Sometimes, they are given intentionally false type annotations to match
# the corresponding z3 function. Reader beware!!

@dataclass
class CVC4Sort:
    name: str

    def __str__(self) -> str:
        return self.name

@dataclass
class CVC4UniverseElement:
    name: str
    sort: CVC4Sort

    def __str__(self) -> str:
        return self.name

    def decl(self) -> CVC4UniverseElementDecl:
        return CVC4UniverseElementDecl(self)

@dataclass
class CVC4UniverseElementDecl:
    elt: CVC4UniverseElement

    def name(self) -> str:
        return self.elt.name

@dataclass
class CVC4AppExpr:
    func: CVC4FuncDecl
    args: List[CVC4UniverseElement]

@dataclass
class CVC4VarDecl:
    name: str
    sort: CVC4Sort

@dataclass
class CVC4FuncDecl:
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
class CVC4Model:
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
