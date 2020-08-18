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
import ast

KODKOD_JAR_EXECUTABLE_PATH = "/Users/amohamdy/stanford/aiken-1920-research/kodkod/kodkod.jar:."
KODKOD_LIBRARY_PATH = "/Users/amohamdy/stanford/aiken-1920-research/kodkod/darwin_x86_64/"
# KodExpr = str
class KodExpr: # KodExpr is either a kodkod Formula or a kodkod Relational Expression
    # Note a KodKod Decl is treated as a formula here
    # For now KodExpr encodes the string that will be written to the java file
    def __init__(self, e: Union[KodExpr, str], is_formula: bool = False):
        if isinstance(e, KodExpr):
            self.expr_str = str(e)
        else:
            self.expr_str = e
        self.is_formula = is_formula
    
    # For now prints that string
    def __str__(self):
        return self.expr_str
    def __repr__(self):
        return self.expr_str

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
    def join_expr(op: str, args: List[KodExpr], is_formula: bool) -> KodExpr:
        if len(args) == 0:
            return KodExpr('', False)
        if len(args) == 1:
            return args[0]
        jop = f'){op}('
        joined_args = jop.join([a.__str__() for a in args[1:]])
        return KodExpr(f'{args[0]}{op}({joined_args})', is_formula)

    @staticmethod
    def relation_to_kod(r: Union[RelationDecl, FunctionDecl, str], index: int) -> KodExpr:
        if isinstance(r, RelationDecl) or isinstance(r, FunctionDecl):
            return KodExpr(f'this.get_relation("{r.name}", {index})')
        return KodExpr(f'this.get_relation("{r}", {index})')

    @staticmethod
    def var_to_kod(sv: SortedVar) -> KodExpr:
        return KodExpr(f'this.get_var("{sv.name}")')

    @staticmethod
    def const_to_kod(c: ConstantDecl, index: int) -> KodExpr:
        return KodExpr(f'this.get_relation("{c.name}", {index})')

    @staticmethod
    def nullary_to_kod(d: RelationDecl, index: int) -> KodExpr:
        return KodExpr(f'this.get_relation("{d.name}", {index})')

    @staticmethod
    def sort_to_kod(s: Sort) -> KodExpr:
        return KodExpr(f'this.sorts.get("{s}")')

    @staticmethod
    def sortdecl_to_kod(s: SortDecl) -> KodExpr:
        return KodExpr(f'this.sorts.get("{s.name}")')

    @staticmethod
    def bool_to_kod(b: Bool) -> KodExpr:
        return KodExpr('Formula.TRUE', True) if b.val else KodExpr('Formula.FALSE', True)

    def _translate_expr(self, e: Expr) -> KodExpr:
        if isinstance(e, KodExpr):
            return e
        if isinstance(e, Bool):
            return KodTranslator.bool_to_kod(e)

        elif isinstance(e, UnaryExpr) and e.op == 'NOT':
            body_expr = self._translate_expr(e.arg)
            assert body_expr.is_formula, f'Not should be applied to a formula not expr: {e.arg}'
            return KodExpr(f'{body_expr}.not()', True)

        elif isinstance(e, UnaryExpr) and e.op == 'NEW':
            assert self.scope.new_allowed()
            with self.scope.next_state_index():
                return self._translate_expr(e.arg)

        elif isinstance(e, BinaryExpr):
            arg1_expr = self._translate_expr(e.arg1)
            arg2_expr = self._translate_expr(e.arg2)
            if e.op == 'IFF' or e.op == 'IMPLIES':
                assert arg1_expr.is_formula and arg2_expr.is_formula
                return KodTranslator.join_expr(f'.{e.op.lower()}', [arg1_expr, arg2_expr], True)
            elif e.op == 'EQUAL': # eq -> iff for relations, functions and bool
                assert arg1_expr.is_formula == arg2_expr.is_formula, f'Equality between Formula and Expression not allowed: {e.arg1}, {e.arg2}'
                if arg1_expr.is_formula: # or arg2_expr.is_formula:
                    return KodTranslator.join_expr('.iff', [arg1_expr, arg2_expr], True)
                else:
                    return KodTranslator.join_expr('.eq', [arg1_expr, arg2_expr], True)

            elif e.op == 'NOTEQ':
                body_expr = self._translate_expr(Eq(e.arg1, e.arg2))
                return KodExpr(f'{body_expr}.not()', True)

            else:
                assert False, f'BinaryExpr: Not found/implemented: {e}'

        elif isinstance(e, NaryExpr) and e.op in ('AND', 'OR'):
            # TODO: op == "DISTINCT"
            kod_args = [self._translate_expr(a) for a in e.args]
            assert all(a.is_formula for a in kod_args), f'Cannot apply AND/OR to non-formulae'
            op = f'.{e.op.lower()}'
            return KodTranslator.join_expr(op, kod_args, True)

        elif isinstance(e, AppExpr):
            d = self.scope.get(e.callee)
            if isinstance(d, DefinitionDecl):
                assert False
            elif isinstance(d, FunctionDecl):
                kod_args = [self._translate_expr(a) for a in e.args]
                to_join = str(KodTranslator.relation_to_kod(d, self.scope.current_state_index))
                for a in reversed(kod_args):
                    to_join = f'{a}.join({to_join})'
                return KodExpr(to_join)
            elif isinstance(d, RelationDecl):
                kod_args = [self._translate_expr(a) for a in e.args]
                assert all(not a.is_formula for a in kod_args), f'Cannot apply relation to a formula: {e}'
                product = KodTranslator.join_expr('.product', kod_args, False)
                callee = KodTranslator.relation_to_kod(d, self.scope.current_state_index)
                return KodTranslator.join_expr('.in', [product, callee], True)
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
                body_expr = self._translate_expr(e.body)
            quant = 'forAll' if e.quant == 'FORALL' else 'forSome'
            sorted_vars = [KodTranslator.join_expr('.oneOf', [v, s], True) for v, s in zip(vs, sorts)]
            # translated = self._translate_expr(NaryExpr('AND', sorted_vars))
            quantified_vars = KodTranslator.join_expr('.and', sorted_vars, False)
            return KodTranslator.join_expr(f'.{quant}', [body_expr, quantified_vars], True)

        elif isinstance(e, IfThenElse):
            branch = self._translate_expr(e.branch)
            then = self._translate_expr(e.then)
            els = self._translate_expr(e.els) 
            assert branch.is_formula, f'If condition must be a formula'
            assert then.is_formula == els.is_formula, f'Then and Else statements must either both be formulae or expressions'

            if not then.is_formula:
                return KodExpr(f'{branch}.thenElse({then}, {els})')

            if_branch = Implies(e.branch, e.then)
            els_branch = Implies(Not(e.branch), e.els)
            return self._translate_expr(And(if_branch, els_branch))

        elif isinstance(e, Id):
            d = self.scope.get(e.name)
            assert d is not None, f'{e.name}\n{e}'
            if isinstance(d, RelationDecl): # Nullary relation : BOOL
                kod_nullary = KodTranslator.relation_to_kod(d, self.scope.current_state_index)
                return KodExpr(f'{kod_nullary}.some()', True)
            elif isinstance(d, ConstantDecl):
                return KodTranslator.const_to_kod(d, self.scope.current_state_index)
            elif isinstance(d, DefinitionDecl):
                assert False
            elif isinstance(d, FunctionDecl):
                assert False, 'impossible since functions have arity > 0'
            elif isinstance(d, SortDecl):
                return self.sortdecl_to_kod(d)
            else:
                expr, = d

                return expr

        else:
            assert False, f'NOT INSTANCE OF ANYTHING: NOT FOUND/IMPLEMENTED: {e}'

class KodSolver:
    def __init__(self, prog: Program, e: Expr, bound: int, num_states: int):
        self.prog: Program = prog
        self.e: Expr = e
        self.bound: int = bound
        self.num_states: int = num_states

        self.translator = self.get_translator(2)

        assert prog.scope is not None
        assert len(prog.scope.stack) == 0
        self.scope = cast(Scope[KodExpr], prog.scope)

        self.class_methods_generators = [ # Order is important here: kod_get_formula must be before kod_get_bounds
          self.kod_get_constructor,
          self.kod_get_get_var,
          self.kod_get_get_relation,
          self.kod_get_get_relation_name,
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
                'kodkod.instance.Tuple',
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
            '       this.relations.get(name).put(index, Relation.nary("__" + index + "__" + name, arity));',
            '   }',
            '   return this.relations.get(name).get(index);',
            '}',
        ]

    def kod_get_get_relation_name(self) -> List[str]:
        return [
            'public String get_relation_name(Relation rel) {',
            '   return rel.name().substring(rel.name().indexOf(\"__\", 2) + 2);',
            '}',
        ]
    
    def get_translator(self, num_states: int) -> KodTranslator:
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
        lines.append('this.sorts.put("__KOD_BOOL__", Relation.unary("__KOD_BOOL__"));')
        for r in self.scope.relations.values():
            if not r.arity: # Nullary Relations are of __KOD_BOOL__ sort
                arity_string = 'Arrays.asList(\"__KOD_BOOL__\")'
            else:
                sorts = [f'"{s}"' for s in r.arity]
                arity_string = f'Arrays.asList({", ".join(sorts)})'
            lines.append(f'this.arities.put("{r.name}", {arity_string});')
        for f in self.scope.functions.values():
            sorts = [f'"{s}"' for s in (*f.arity, f.sort)]
            arity_string = f'Arrays.asList({", ".join(sorts)})'
            lines.append(f'this.arities.put("{f.name}", {arity_string});')
        for c in self.scope.constants.values():
            arity_string = f'Arrays.asList("{c.sort}")'
            lines.append(f'this.arities.put("{c.name}", {arity_string});')

        lines.append("}\n")
        return lines

    def kod_get_bounds(self) -> List[str]:
        lines: List[str] = [
          'public Bounds bounds() {',
        ]
        atoms = [f'"{s.name}{i}"' for s in self.scope.sorts.values() for i in range(self.bound)]
        atoms.extend(['\"__KOD_TRUE__\", \"__KOD_FALSE__\"'])
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
        lines.append(f'_b.boundExactly(this.sorts.get(\"__KOD_BOOL__\"), _f.setOf(\"__KOD_TRUE__\", \"__KOD_FALSE__\"));')
        # Bound relations to their arity
        lines.extend([
            'for(Map<Integer, Relation> m : this.relations.values()) {',
            '   for(Relation rel: m.values()){',
            '      Iterator<String> it = this.arities.get(this.get_relation_name(rel)).iterator();',
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

        lines.append('return _b;')
        lines.append('}\n')
        return lines

# TODO: Change back quotes to single quotes
    def kod_get_main(self) -> List[str]:
        lines: List[str] = [
            'public static void main(String[] args) {',
            '   final _KodkodModel model = new _KodkodModel();',
            '   final Solver solver = new Solver();',
            '   solver.options().setSolver(SATFactory.MiniSat);',
            '   final Solution sol = solver.solve(model.formula(), model.bounds());',
            '   String out = String.format("{\\n`outcome`: `%s`,\\n`instance`:{\\n", sol.outcome());',
            '   if (sol.sat()) {',
            '      for (Map.Entry<Relation, TupleSet> me : sol.instance().relationTuples().entrySet()) {',
            '         out += String.format("`%s`: [", me.getKey());',
            '         Iterator<Tuple> it = me.getValue().iterator();',
            '         while (it.hasNext()) {',
            '            out += "[";',
            '            Tuple t = it.next();',
            '            for (int i = 0; i < t.arity(); i++) {',
            '            out += String.format("`%s`, ", t.atom(i));',
            '         }',
            '         out += "],";',
            '         }',
            '      out += "],\\n";',
            '      }',
            '   }',
            '   out += String.format("\\n},\\n`proof`: `%s`\\n}", sol.proof());',
            '   out = out.replace(\'`\', \'"\');',
            '   System.out.println(out);',
            '}'
        ]
        return lines

    def kod_get_class(self) -> List[str]:
        lines: List[str] = [
            'public final class _KodkodModel {',
            'private final Map<String, Variable> vars;',
            'private final Map<String, Map<Integer, Relation>> relations;',
            'private final Map<String, List<String>> arities;',
            'private final Map<String, Relation> sorts;',
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

def kod_check_sat(prog: Program, f: Expr, bound: int, num_states: int) -> bool: # -> Dict[String, Union(List[List[str]], str)]
    '''
    Returns True if f is sat
    '''
    start = datetime.now()
    solver = KodSolver(prog, f, bound, num_states)
    open('_KodkodModel.java', 'w').write('\n'.join(solver.get_java_code()))
    end = datetime.now()
    print(f'py -> java translation: {(end - start).microseconds / 1000}ms')
    cmd = ['javac', '-cp', KODKOD_JAR_EXECUTABLE_PATH, '_KodkodModel.java']
    subprocess.check_call(cmd)
    cmd = ['java', '-cp', KODKOD_JAR_EXECUTABLE_PATH, f'-Djava.library.path={KODKOD_LIBRARY_PATH}', '_KodkodModel']
    out = subprocess.check_output(cmd, text=True)
    print('out:', out)
    out = ast.literal_eval(out)
    # for entry in out['instance']:
    #     val = out['instance'][entry]
    #     for atom in val:
    #         print(f'{atom} part of {val} in {entry}')
    return out['outcome'] in ['SATISFIABLE', 'TRIVIALLY_SATISFIABLE']

    '''
            out: {
            "outcome": "SATISFIABLE",
            "instance":{
            "server": [["server0"],["server1"],["server2"],],
            "client": [["client0"],["client1"],["client2"],],
            "idx": [["idx0"],["idx1"],["idx2"],],
            "request_msg": [["client0""server2""idx2"],["client2""server2""idx2"],],
            "request_msg": [["client0""server2""idx2"],],
            "grant_msg": [],
            "grant_msg": [["client2""server2""idx2"],],
            "release_msg": [],
            "release_msg": [],
            "semaphore": [["server1"],["server2"],],
            "semaphore": [["server1"],],
            "used": [["idx1"],],
            "used": [["idx1"],],
            "holds_lock": [["client2""server2"],],
            "holds_lock": [["client2""server2"],],
            "$c": [["client2"],],
            "$s": [["server2"],],
            "$id": [["idx2"],],
            "$C1": [["client2"],],
            "$S": [["server2"],],
            "$C2": [["client2"],],
            "$I2": [["idx2"],],

            },
            "proof": "null"
            }
        univ = {'server': ('server0', 'server1', 'server2'), 'client': ('client0', ..)}
        relations = {
            '_0_holds_lock': {('client0', 'server2'): True, ('client0', 'server0'): False, ...},
            '_1_holds_lock': {},
        }
'''

def kod_verify(_solver: Solver) -> None:
    '''
    '''
    prog = syntax.the_program
    print(f'\n[{datetime.now()}] [PID={os.getpid()}] Starting kod_verify\n')

    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # convert to CNF
    # safety = [inv.expr for inv in prog.invs() if inv.is_safety]
    invs = [inv.expr for inv in prog.invs() if not inv.is_safety]


    for inv in invs:
        f = And(*inits, Not(inv))
        print(f'CHECKING INIT IMPLIES {inv}')
        res = kod_check_sat(prog, f, utils.args.bound if utils.args.bound is not None else 1, 1)

        if res:
            print('  invariant not implied by init')
        else:
            print(f'GOOD')

    for ition in prog.transitions():
        for inv in invs:
            f = And(*invs, ition.as_twostate_formula(prog.scope), New(Not(inv)))
            print(f'CHECKING transition {ition.name} IMPLIES {inv}')
            res = kod_check_sat(prog, f, utils.args.bound if utils.args.bound is not None else 1, 2)

            if res:
                print('  invariant not implied by init')
            else:
                print(f'GOOD')



def add_argparsers(subparsers: argparse._SubParsersAction) -> Iterable[argparse.ArgumentParser]:
    result : List[argparse.ArgumentParser] = []

    # forward_explore_inv
    s = subparsers.add_parser('kod-verify', help='Verify model using KodKod')
    s.set_defaults(main=kod_verify)
    result.append(s)

    for s in result:
        s.add_argument('--bound', type=int, help='Maximum bounds to use for bounded kodkod model.')

    return result

'''
NOTES
In a transition there's exactly 2 states
'''