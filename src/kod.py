from __future__ import annotations

import argparse
import itertools
from itertools import product, chain, combinations, repeat
from functools import reduce
from collections import defaultdict
from pathlib import Path
import pickle
import sys
import os
import math
import multiprocessing
import multiprocessing.connection
from contextlib import nullcontext
import random
from random import randint
import queue
from datetime import datetime, timedelta
from hashlib import sha1
from dataclasses import dataclass

from syntax import *
from logic import *

from typing import TypeVar, Iterable, FrozenSet, Union, Callable, Generator, Set, Optional, cast, Type, Collection, TYPE_CHECKING, AbstractSet

KODKOD_JAR_EXECUTABLE_PATH = "/Users/amohamdy/stanford/aiken-1920-research/kodkod/kodkod.jar:."
KODKOD_LIBRARY_PATH = "/Users/amohamdy/stanford/aiken-1920-research/kodkod/darwin_x86_64/"
KodExpr = str
class KodTranslator:
    def __init__(self, prog: Program, num_states: int):
        self.prog = prog
        self.num_states = num_states

        assert prog.scope is not None
        assert len(prog.scope.stack) == 0
        self.scope = cast(Scope[KodExpr], prog.scope)

    def translate_expr(self, expr: Expr) -> KodExpr:
        assert self.scope.num_states == 0, self.scope.num_states
        assert self.scope.current_state_index == 0, self.scope.current_state_index
        with self.scope.n_states(self.num_states):
            return self._translate_expr(expr)

    @staticmethod
    def join_expr(op: str, args: List[KodExpr]) -> KodExpr:
        if len(args) == 0:
            return ''
        if len(args) == 1:
            return args[0]
        jop = f'){op}('
        joined_args = jop.join(args[1:])
        return f'{args[0]}{op}({joined_args})'

    @staticmethod
    def relation_to_kod(r: RelationDecl, index: int) -> KodExpr:
        return f'this.get_relation("{r.name}", {index})'

    @staticmethod
    def var_to_kod(sv: SortedVar) -> KodExpr:
        return f'this.get_var("{sv.name}")'

    @staticmethod
    def const_to_kod(c: ConstantDecl) -> KodExpr:
        return f'this.get_var("{c.name}")'

    @staticmethod
    def nullary_to_kod(d: RelationDecl, index: int) -> KodExpr:
        if not d.mutable:
            index = 0
        return f'this.get_relation("{d.name}", {index})'

    @staticmethod
    def sort_to_kod(s: Sort) -> KodExpr:
        return f'this.sorts.get("{s}")'

    @staticmethod
    def sortdecl_to_kod(s: SortDecl) -> KodExpr:
        return f'this.sorts.get("{s.name}")'

    @staticmethod
    def bool_to_kod(b: Bool) -> KodExpr:
        return 'Formula.TRUE' if b.val else 'Formula.FALSE'

    def _translate_expr(self, e: Expr) -> KodExpr:
        if isinstance(e, Bool):
            return KodTranslator.bool_to_kod(e)

        elif isinstance(e, UnaryExpr) and e.op == 'NOT':
            body = self._translate_expr(e.arg)
            return f'{body}.not()'

        elif isinstance(e, UnaryExpr) and e.op == 'NEW':
            assert self.scope.new_allowed()
            with self.scope.next_state_index():
                return self._translate_expr(e.arg)

        # TODO: CHANGE TO ELIFs and don't leave it open-ended
        elif isinstance(e, BinaryExpr):
            arg1 = self._translate_expr(e.arg1)
            arg2 = self._translate_expr(e.arg2)
            op = ''
            endop = ''
            if e.op == 'EQUAL':
                op = '.eq'
            elif e.op == 'NOTEQ':
                op = '.eq'
                endop = '.not()'
            else:
                op = f'.{e.op.lower()}'
            return KodTranslator.join_expr(op, [arg1, arg2]) + endop

        elif isinstance(e, NaryExpr) and e.op in ('AND', 'OR'):
            # TODO: op == "DISTINCT"
            args = [f'({self._translate_expr(a)})' for a in e.args]
            op = f'.{e.op.lower()}'
            return KodTranslator.join_expr(op, args)

        elif isinstance(e, AppExpr):
            d = self.scope.get(e.callee)
            if isinstance(d, DefinitionDecl):
                assert False
            elif isinstance(d, FunctionDecl):
                kod_args = [self._translate_expr(a) for a in e.args]
                callee = KodTranslator.relation_to_kod(d, self.scope.current_state_index)
                return KodTranslator.join_expr('.join', list(reversed(kod_args)) + [callee])
            elif isinstance(d, RelationDecl):
                kod_args = [self._translate_expr(a) for a in e.args]
                product = KodTranslator.join_expr('.product', kod_args)
                callee = KodTranslator.relation_to_kod(d, self.scope.current_state_index)
                return f'{product}.in({callee})'
            else:
                assert False, f'{d}\n{e}'

        elif isinstance(e, QuantifierExpr): # and e.quant in self.Kod_QUANT:
            vs = []
            sorts = []
            for sv in e.binder.vs:
                assert sv.sort is not None and not isinstance(sv.sort, syntax.SortInferencePlaceholder)
                vs.append(self.var_to_kod(sv))
                sorts.append(self.sort_to_kod(sv.sort))
            with self.scope.in_scope(e.binder, vs):
                body = self._translate_expr(e.body)
            quant = 'forAll' if e.quant == 'FORALL' else 'forSome'
            sorted_vars = [f'{v}.oneOf({s})' for v, s in zip(vs, sorts)]
            # translated = self.__translate_expr(NaryExpr('AND', sorted_vars))
            quantified = KodTranslator.join_expr('.and', sorted_vars)
            return f'{body}.{quant}({quantified})'

        elif isinstance(e, Id):
            d = self.scope.get(e.name)
            assert d is not None, f'{e.name}\n{e}'
            if isinstance(d, RelationDecl): # Nullary relation : BOOL
                kod_nullary = KodTranslator.nullary_to_kod(d, self.scope.current_state_index)
                return f'this.__KodBoolUnity__.intersection({kod_nullary}).some()'
            elif isinstance(d, ConstantDecl):
                return KodTranslator.const_to_kod(d)
            elif isinstance(d, DefinitionDecl):
                assert False
            elif isinstance(d, FunctionDecl):
                assert False, 'impossible since functions have arity > 0'
            elif isinstance(d, SortDecl):
                return self.sortdecl_to_kod(d)
            else:
                x, = d
                return x

        else:
            assert False, f'NOT FOUND/IMPLEMENTED: {e}'

class KodSolver:
    def __init__(self, prog: Program, e: Expr, bound: int):
        self.prog: Program = prog
        self.e: Expr = e
        self.bound: int = bound
        # self.num_states = num_states

        self.translator = self.get_translator(1)

        assert prog.scope is not None
        assert len(prog.scope.stack) == 0
        self.scope = cast(Scope[KodExpr], prog.scope)

        self.class_methods_generators = [ # Order is important here: kod_get_formula must be before kod_get_bounds
          self.kod_get_constructor,
          self.kod_get_get_var,
          self.kod_get_get_relation,
          self.kod_get_formula,
          self.kod_get_bounds,
          self.kod_get_main,
        ]

    def get_dependencies(self) -> List[str]:
        return ['java.util.ArrayList',
                'java.util.List',
                'java.util.Map',
                'java.util.HashMap',
                'java.util.Arrays',
                'java.util.Iterator',
                'kodkod.ast.Formula',
                'kodkod.ast.Relation',
                'kodkod.ast.Expression',
                'kodkod.ast.Variable',
                'kodkod.engine.Solution',
                'kodkod.engine.Solver',
                'kodkod.engine.satlab.SATFactory',
                'kodkod.instance.Bounds',
                'kodkod.instance.TupleFactory',
                'kodkod.instance.TupleSet',
                'kodkod.instance.Universe',
                ]

    def kod_get_get_var(self) -> List[str]:
        return [
            'public Variable get_var(String name) {',
            '  if(!this.vars.containsKey(name)) {',
            '    vars.put(name, Variable.unary(name));',
            '  }',
            '  return this.vars.get(name);',
            '}',
        ]
    
    def kod_get_get_relation(self) -> List[str]:
        return [
            'public Relation get_relation(String name, int index) {',
            '   if (!this.relations.containsKey(name)) {',
            '      relations.put(name, new HashMap<Integer, Relation>());',
            '   }',
            '   if (!this.relations.get(name).containsKey(index)) {',
            '       int arity = this.arities.get(name).size() == 0? 1: this.arities.get(name).size();',
            '       this.relations.get(name).put(index, Relation.nary(name, arity));',
            '   }',
            '   return this.relations.get(name).get(index);',
            '}',
        ]
    def get_translator(self, num_states: int) -> KodTranslator:
        # TODO: support multiple states
        assert num_states == 1
        return KodTranslator(self.prog, num_states)

    def kod_get_formula(self) -> List[str]:
        kod_formula = self.translator.translate_expr(self.e)
        lines = ['public Formula formula() {',
          f'// {self.e}']
        lines.append(f'return {kod_formula};')
        lines.append('}')
        return lines

    def kod_get_constructor(self) -> List[str]:
        lines = ["public _KodkodModel() {"]
        lines.extend([
            'this.vars = new HashMap<String, Variable>();',
            'this.relations = new HashMap<String, Map<Integer, Relation>>();',
            'this.arities = new HashMap<String, List<String>>();',
            'this.sorts = new HashMap<String, Relation>();',
        ])
        lines.extend(f'this.sorts.put("{s.name}", Relation.unary("{s.name}"));' for s in self.scope.sorts.values())
        for r in self.scope.relations.values():
            sorts = [f'"{s}"' for s in r.arity]
            arity_string = f'Arrays.asList({", ".join(sorts)})'
            lines.append(f'this.arities.put("{r.name}", {arity_string});')
        lines.extend(f'this.arities.put("{f.name}", Relation.nary("{f.name}", {len(f.arity) + 1}));'
            for f in self.scope.functions.values())
        lines.append('this.__KodBoolUnity__ = Relation.unary(\"__KodBoolUnity__\");')
        lines.append("}\n")
        return lines

    def kod_get_bounds(self) -> List[str]:
        lines: List[str] = [
          'public Bounds bounds() {',
        ]
        atoms = [f'"{s.name}{i}"' for s in self.scope.sorts.values() for i in range(self.bound)]
        atoms.append('\"__KODBOOLUNITY__"')
        atoms_string = ', '.join(atoms)
        lines.extend([
            f'final Universe _univ = new Universe(Arrays.asList({atoms_string}));',
            'final TupleFactory _f  = _univ.factory();',
            'final Bounds _b = new Bounds(_univ);',
        ])
        # Bound sorts
        lines.extend(
          f'_b.boundExactly(this.sorts.get("{s.name}"), _f.range(_f.tuple("{s.name}0"), _f.tuple("{s.name}{self.bound - 1}")));'
          for s in self.scope.sorts.values()
        )
        lines.append('_b.boundExactly(this.__KodBoolUnity__, _f.setOf(_f.tuple("__KODBOOLUNITY__")));')
        # Bound relations to their arity
        lines.extend([
            'for(Map<Integer, Relation> m : this.relations.values()) {',
            '   for(Relation rel: m.values()){',
            '      Iterator<String> it = this.arities.get(rel.name()).iterator();',
            '      if(!it.hasNext()) { // Nullary relation',
            '         _b.bound(rel, _f.setOf(_f.tuple("__KODBOOLUNITY__")));',
            '      } else {',
            '         TupleSet up_bounds = _b.upperBound(this.sorts.get(it.next())); ',
            '         while(it.hasNext()) {',
            '            up_bounds = up_bounds.product(_b.upperBound(this.sorts.get(it.next())));',
            '         }',
            '         _b.bound(rel, up_bounds);',
            '      }',

            '   }',
            '}',
        ])

        # Bound functions to their arity/sorts
        for f in self.scope.functions.values():
            kod_func = f'this.relations.get("{f.name}")' #self.translator.translate_expr(r)
            bound_list = [f'_b.upperBound(this.sorts.get("{s}"))' for s in f.arity + [f.sort]]
            up_bound = KodTranslator.join_expr('.product', bound_list)
            lines.append(f'_b.bound({kod_func}, {up_bound});')

        lines.append('return _b;')
        lines.append('}\n')
        return lines

    def kod_get_main(self) -> List[str]:
        lines: List[str] = [
            'public static void main(String[] args) {',
            'final _KodkodModel model = new _KodkodModel();',
            'final Solver solver = new Solver();',
            'solver.options().setSolver(SATFactory.MiniSat);',
            'final Solution sol = solver.solve(model.formula(), model.bounds());',
            'System.out.println(sol);',
            'String json = \"{\\\"outcome\\\": \\\"%s\\\",\\n\\\"instance\\\": \\\"%s\\\",\\n\\\"proof\\\": \\\"%s\\\",\\n\\\"stats\\\": \\\"%s\\\"}\";',
            'json = String.format(json, sol.outcome(), sol.instance(), sol.proof(), sol.stats());',
            'System.out.println(json);',
        ]
        lines.append('}')
        return lines

    def kod_get_class(self) -> List[str]:
        lines: List[str] = [
            'public final class _KodkodModel {',
            'private final Map<String, Variable> vars;',
            'private final Map<String, Map<Integer, Relation>> relations;',
            'private final Map<String, List<String>> arities;',
            'private final Map<String, Relation> sorts;',
            'private final Relation __KodBoolUnity__;',
        ]
        lines.extend(chain(*(g() for g in self.class_methods_generators)))
        lines.append("}")
        return lines

    def get_java_code(self) -> List[str]:
        lines: List[str] = []
        # write modules' imports
        lines.extend(f'import ' + module +';' for module in self.get_dependencies())
        lines.extend(self.kod_get_class())
        return lines

def kod_check_sat(prog: Program, f: Expr, bound: int) -> bool:
    '''
    Returns True if f is sat
    '''
    start = datetime.now()
    solver = KodSolver(prog, f, bound)
    open('_KodkodModel.java', 'w').write('\n'.join(solver.get_java_code()))
    end = datetime.now()
    print(f'py -> java translation: {(end - start).microseconds / 1000}ms')
    cmd = ['javac', '-cp', KODKOD_JAR_EXECUTABLE_PATH, '_KodkodModel.java']
    subprocess.check_call(cmd)
    cmd = ['java', '-cp', KODKOD_JAR_EXECUTABLE_PATH, f'-Djava.library.path={KODKOD_LIBRARY_PATH}', '_KodkodModel']
    out = subprocess.check_output(cmd, text=True)
    print(out)
    return False

def kod_verify(_solver: Solver) -> None:
    '''
    '''
    prog = syntax.the_program
    print(f'\n[{datetime.now()}] [PID={os.getpid()}] Starting kod_verify\n')

    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # convert to CNF
    safety = [inv.expr for inv in prog.invs() if inv.is_safety]
    invs = [inv.expr for inv in prog.invs() if not inv.is_safety]

    for inv in invs:
        f = And(*inits, Not(inv))
        print(f'CHECKING INIT IMPLIES {inv}')
        res = kod_check_sat(prog, f, utils.args.bound if utils.args.bound is not None else 1)

        if res:
            print('  invariant not implied by init')
        else:
            print(f'GOOD')

def add_argparsers(subparsers: argparse._SubParsersAction) -> Iterable[argparse.ArgumentParser]:
    result : List[argparse.ArgumentParser] = []

    # forward_explore_inv
    s = subparsers.add_parser('kod-verify', help='Verify invariants using KodKod')
    s.set_defaults(main=kod_verify)
    result.append(s)

    for s in result:
        s.add_argument('--bound', type=int, help='Maximum bounds to use for bounded kodkod model.')

    return result
