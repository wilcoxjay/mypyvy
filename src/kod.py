from __future__ import annotations

import argparse
import itertools
from itertools import product, chain, combinations, repeat
from functools import reduce
from collections import defaultdict
from os import remove
from pathlib import Path
import pickle
# from stubs.z3 import unknown
import sys
import os
import math
from multiprocessing import Lock, cpu_count
from multiprocessing.pool import ThreadPool
import multiprocessing.connection
from contextlib import nullcontext
import random
from random import randint
import queue
from datetime import datetime, timedelta
from hashlib import sha1
from dataclasses import dataclass
from threading import Thread
from colorama import Fore
import subprocess

from syntax import *
from logic import *
import threading

from typing import TypeVar, Iterable, FrozenSet, Union, Callable, Generator, Set, Optional, cast, Type, Collection, TYPE_CHECKING, AbstractSet
from ast import literal_eval
import pandas as pd

KODKOD_JAR_EXECUTABLE_PATH = '/scr/padon/kodkod/kodkod.jar:.'
KODKOD_LIBRARY_PATH = '/scr/padon/kodkod/'
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
    def __str__(self) -> str:
        return self.expr_str
    def __repr__(self) -> str:
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
    def relation_to_kod(
            r: Union[RelationDecl, FunctionDecl, ConstantDecl],
            expr_type: str,
            index: int
        ) -> KodExpr:
        if not r.mutable:
            index = 0
        return KodExpr(f'this.get_expression("{r.name}", "{expr_type}", {index})')
        
    @staticmethod
    def var_to_kod(sv: SortedVar) -> KodExpr:
        return KodExpr(f'this.get_var("{sv.name}")')

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
                assert False, (e,d)
            elif isinstance(d, FunctionDecl):
                kod_args = [self._translate_expr(a) for a in e.args]
                to_join = str(KodTranslator.relation_to_kod(d, 'FUNCTION', self.scope.current_state_index))
                for a in reversed(kod_args):
                    to_join = f'{a}.join({to_join})'
                return KodExpr(to_join)
            elif isinstance(d, RelationDecl):
                kod_args = [self._translate_expr(a) for a in e.args]
                assert all(not a.is_formula for a in kod_args), f'Cannot apply relation to a formula: {e}'
                product = KodTranslator.join_expr('.product', kod_args, False)
                callee = KodTranslator.relation_to_kod(d, 'RELATION', self.scope.current_state_index)
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
                assert False, 'Example with expressions for thenElse'
                return KodExpr(f'{branch}.thenElse({then}, {els})') # TODO: NOT TESTED

            if_branch = Implies(e.branch, e.then)
            els_branch = Implies(Not(e.branch), e.els)
            return self._translate_expr(And(if_branch, els_branch))

        elif isinstance(e, Id):
            d = self.scope.get(e.name)
            assert d is not None, f'{e.name}\n{e}'
            if isinstance(d, RelationDecl): # Nullary relation : BOOL
                kod_nullary = KodTranslator.relation_to_kod(d, 'RELATION', self.scope.current_state_index)
                return KodExpr(f'{kod_nullary}.some()', True)
            elif isinstance(d, ConstantDecl):
                return KodTranslator.relation_to_kod(d, 'CONSTANT', self.scope.current_state_index)
            elif isinstance(d, DefinitionDecl):
                assert False, d
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
    def __init__(self, prog: Program, class_name: str, e: Expr, bound: int, num_states: int, one_bound=False):
        self.prog: Program = prog
        self.class_name = class_name
        self.e: Expr = e
        self.bound: int = bound
        self.num_states: int = num_states
        self.one_bound: int = one_bound

        self.translator = self.get_translator(2)

        assert prog.scope is not None
        assert len(prog.scope.stack) == 0
        self.scope = cast(Scope[KodExpr], prog.scope)

        self.class_methods_generators: List[Callable[...,List[str]]] = [ # Order is important here: kod_get_formula must be before kod_get_bounds
          self.kod_get_constructor,
          self.kod_get_get_var,
          self.kod_get_get_expression,
          self.kod_get_get_relation_name,
          self.kod_get_formula,
          self.kod_get_spec,
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
                'java.util.Collection',
                'java.io.*',
                'kodkod.ast.Formula',
                'kodkod.ast.Relation',
                'kodkod.ast.Expression',
                'kodkod.ast.Variable',
                'kodkod.ast.Decls',
                'kodkod.engine.Solution',
                'kodkod.engine.Solver',
                'kodkod.engine.satlab.SATFactory',
                'kodkod.instance.Bounds',
                'kodkod.instance.TupleFactory',
                'kodkod.instance.TupleSet',
                'kodkod.instance.Tuple',
                'kodkod.instance.Universe',
                ]

    def kod_get_constructor(self) -> List[str]:
        lines = [f'public {self.class_name}() {{']
        lines.extend([
            'this.arities = new HashMap<String, List<String>>();',
            'this.vars = new HashMap<String, Variable>();',
            'this.relations = new HashMap<String, Map<Integer, Relation>>();',
            'this.functions = new HashMap<String, Map<Integer, Relation>>();',
            'this.constants = new HashMap<String, Map<Integer, Relation>>();',
            'this.sorts = new HashMap<String, Relation>();',
        ])
        lines.append('this.sorts.put("__KOD_BOOL__", Relation.unary("__KOD_BOOL__"));')
        lines.extend(f'this.sorts.put("{s.name}", Relation.unary("{s.name}"));' for s in self.scope.sorts.values())
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

    def kod_get_get_var(self) -> List[str]:
        return [
            'public Variable get_var(String name) {',
            '  if(!this.vars.containsKey(name)) {',
            '    vars.put(name, Variable.unary(name));',
            '  }',
            '  return this.vars.get(name);',
            '}',
        ]
    def kod_get_get_expression(self) -> List[str]:
        return [

            'public Relation get_expression(String name, String type, int index) {',
            '   final Map<String, Map<Integer, Relation>> m;',
            '   switch(type)',
            '   {',
            '      case "RELATION": m = this.relations; break;',
            '      case "FUNCTION": m = this.functions; break;',
            '      case "CONSTANT": m = this.constants; break;',
            '      default: m = this.constants;; // TODO: Raise Exception',
            '   }',
            '   if (!m.containsKey(name)) {',   
            '      m.put(name, new HashMap<Integer, Relation>());', 
            '   }', 
            '   if (!m.get(name).containsKey(index)) {',    
            '      int arity = this.arities.get(name).size() == 0? 1: this.arities.get(name).size();',  
            '      m.get(name).put(index, Relation.nary("__" + index + "__" + name, arity));',  
            '   }', 
            '   return m.get(name).get(index);',    
            '}',    
        ]

    def kod_get_get_relation_name(self) -> List[str]:
        return [
            'public String get_relation_name(Relation rel) {',
            '   return rel.name().substring(rel.name().indexOf(\"__\", 2) + 2);',
            '}',
        ]
    
    def kod_get_formula(self) -> List[str]:
        kod_formula = self.translator.translate_expr(self.e)
        lines = ['public Formula formula() {',
          f'// {self.e}']
        lines.append(f'return {kod_formula};')
        lines.append('}')
        return lines

    def kod_get_spec(self) -> List[str]: # Should modify this later to also include axioms
        return [
            'public Formula spec() {',
            '   // Function (modeled as kodkod relations) in mypyvy have a total ordering',
            '   List<Formula> functions_spec = new ArrayList<Formula>();',
            '   for(Map<Integer, Relation> m : this.functions.values()) {',
            '      for(Relation f : m.values()) {',
            '         Expression joined = f;',
            '         // Last sort is sort of range',
            '         List<String> function_arguments = arities.get(get_relation_name(f))',
            '                                             .subList(0, arities.get(get_relation_name(f)).size() - 1);',
            '         assert function_arguments.size() > 0;',
            '         joined = get_var("X0").join(joined);',
            '         Decls dcls = get_var("X0").oneOf(sorts.get(function_arguments.get(0)));',
            '         for(int ind = 1; ind < function_arguments.size(); ind++) {',
            '            joined = get_var("X" + ind).join(joined);',
            '            dcls = dcls.and(get_var("X" + ind).oneOf(sorts.get(function_arguments.get(ind))));',
            '         }',
            '         functions_spec.add(joined.one().forAll(dcls));',
            '      }',
            '   }',
            '   final Formula functions_totality = Formula.and(functions_spec);',

            '   // Constants (modeled as kodkod relations) must contain exactly one value',
            '   List<Formula> constants_spec = new ArrayList<Formula>();',
            '   for(Map<Integer, Relation> m : constants.values()) {',
            '       for(Relation r : m.values()) {',
            '            constants_spec.add(r.one());',
            '       }',
            '   }',
            '   final Formula constants_singularity = Formula.and(constants_spec);',

            '   return Formula.and(functions_totality, constants_singularity);',
            '}',
        ]

    def kod_get_bounds(self) -> List[str]:
        lines: List[str] = [
            'public Bounds bounds(int _bound) {',
            '   List<String> atoms = new ArrayList<>(((sorts.size() - 1) * _bound) + 1); // -1 for __KOD_BOOL__',
            '   for(Relation sort: sorts.values()) {',
            '      for(int i = 0; i < _bound; i++) {',
            '         atoms.add(sort.name() + i);',
            '      }',
            '   }',
            '   atoms.add("__KOD_TRUTH__");',
            '   final Universe _univ = new Universe(atoms);',
            '   final TupleFactory _f  = _univ.factory();',
            '   final Bounds _b = new Bounds(_univ);',
        ]
        # Bound sorts
        lines.extend(
          f'_b.boundExactly(this.sorts.get("{s.name}"), _f.range(_f.tuple("{s.name}0"), _f.tuple("{s.name}" + (_bound - 1))));'
          for s in self.scope.sorts.values()
        )
        lines.append(f'_b.boundExactly(this.sorts.get(\"__KOD_BOOL__\"), _f.setOf(\"__KOD_TRUTH__\"));')
        # Bound relations to their arity
        lines.extend([
            'final Map<String, Map<Integer, Relation>> mapOfExprs = new HashMap<>(this.relations);',
            'mapOfExprs.putAll(this.functions);',
            'mapOfExprs.putAll(this.constants);',
            'for(Map<Integer, Relation> m : mapOfExprs.values()) {',
            '   for(Relation rel: m.values()){',
            '      Iterator<String> it = this.arities.get(this.get_relation_name(rel)).iterator();',
            '      if(it.hasNext()) {',
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
            f'   final {self.class_name} model = new {self.class_name}();',
            '   final Solver solver = new Solver();',
            # '   final Writer stdout = new PrintWriter(System.out);',
            '   solver.options().setSolver(SATFactory.MiniSat);',
            f'   for(int i = {self.bound if self.one_bound else 1}; i <= {self.bound}; i++) {{',
            '      final Solution sol = solver.solve(Formula.and(model.formula(), model.spec()), model.bounds(i));',
            '      String out = String.format("{`bound`: %d, `outcome`: `%s`, `translation_time`: %s, `solving_time`: %s}", i, sol.outcome(), sol.stats().translationTime(), sol.stats().solvingTime());',
            '      out = out.replace(\'`\', \'"\');',
            '      try {',
            '         FileWriter writer = new FileWriter("_KOD_RESULTS" + File.separator + model.getClass().getName() + "__" + i + ".kod.result", false);',
            '         writer.write(out);',
            '         writer.flush();',
            '         writer.close();',
            # '         stdout.append(out);',
            # '         stdout.flush();',
            '      } catch(IOException ex) {',
            '         System.out.println(ex);',
            '         System.out.println("{outcome: \'WRITER_ERROR\'},");',
            '      }',
            '      if(sol.sat()) {',
            '         break;',
            '      }',
            '   }',
            '}',
        ]
        return lines

    def kod_get_class(self) -> List[str]:
        lines: List[str] = [
            f'public final class {self.class_name} {{',
            'private final Map<String, List<String>> arities;',
            'private final Map<String, Variable> vars;',
            'private final Map<String, Map<Integer, Relation>> relations;',
            'private final Map<String, Map<Integer, Relation>> functions;',
            'private final Map<String, Map<Integer, Relation>> constants;',
            'private final Map<String, Relation> sorts;',
        ]
        lines.extend(chain(*(g() for g in self.class_methods_generators)))
        lines.append("}")
        return lines

    def get_translator(self, num_states: int) -> KodTranslator:
        return KodTranslator(self.prog, num_states)


    def get_java_code(self) -> List[str]:
        lines: List[str] = []
        # get modules' imports
        lines.extend(f'import ' + module +';' for module in self.get_dependencies())
        lines.extend(self.kod_get_class())
        return lines

def kod_check_sat(
        prog: Program,
        f: Expr,
        bound: int,
        num_states: int,
        file_name: str,
        one_bound: bool =False,
        ) -> None:
    '''
    '''
    java_file_name = file_name + '.java'
    assert not os.path.isfile(java_file_name)

    solver = KodSolver(prog, file_name, f, bound, num_states, one_bound)

    java_lines = solver.get_java_code()

    with open(java_file_name, 'w') as f:
        f.write('\n'.join(java_lines))

def kod_verify(_solver: Solver) -> None:
    '''
    '''
    prog = syntax.the_program
    print(f'\n[{datetime.now()}] [PID={os.getpid()}] Starting kod_verify\n')

    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # convert to CNF
    invs = [inv.expr for inv in prog.invs() if not inv.is_safety]

    for inv in invs:
        f = And(*inits, Not(inv))
        print(f'CHECKING INIT IMPLIES {inv}')
        # res = kod_check_sat(
        #             prog,
        #             f,
        #             utils.args.bound if utils.args.bound else 1,
        #             1,
        #             one_bound=True)[0]

        # if res['outcome'] in ('SATISFIABLE', 'TRIVIALLY_SATISFIABLE'):
        #     print('  invariant not implied by init')
        # else:
        #     print(f'GOOD')

    for ition in prog.transitions():
        for inv in invs:
            # f = And(*invs, ition.as_twostate_formula(prog.scope), New(Not(inv)))
            # print(f'CHECKING transition {ition.name} IMPLIES {inv}')
            # res = kod_check_sat(
            #             prog,
            #             f,
            #             utils.args.bound if utils.args.bound is not None else 1,
            #             2,
            #             one_bound=True)[0]

            # if res['outcome'] in ('SATISFIABLE', 'TRIVIALLY_SATISFIABLE'):
            #     print('  invariant not implied by init')
            # else:
            #     print(f'GOOD')
            print('Checking ition')
    
def get_class_name(filename: str) -> str:
    kod_class_name = os.path.splitext(os.path.basename(filename))[0]
    kod_class_name = kod_class_name.replace('-', '_')
    return kod_class_name

MAXIMUM_SATISFIABILITY_BOUND = 10
def kod_bench_with(
        solver: Solver,
        ition: DefinitionDecl,
        remove_index: Optional[int],
        check_index: int
        ) -> None:
    prog = syntax.the_program
    invs = [inv.expr for inv in prog.invs()] 
    pre_invs = [inv for counter, inv in enumerate(invs) if counter != remove_index]      
    class_name = get_class_name(utils.args.filename)
    file_name = f'{class_name}__{ition.name}__{remove_index}__{check_index}'

    axioms = [a.expr for a in prog.axioms()]
    f = And(*axioms, *pre_invs, ition.as_twostate_formula(prog.scope), New(Not(invs[check_index])))

    kod_check_sat(prog, f, MAXIMUM_SATISFIABILITY_BOUND, 2, file_name)

def kod_benchmark(_solver: Solver) -> None:
    prog = syntax.the_program
    print(f'[{datetime.now()}] [PID={os.getpid()}] Starting benchmark on {os.path.basename(utils.args.filename)}')
    invs = [inv.expr for inv in prog.invs()]

    if not os.path.exists('_KOD_RESULTS'):
        os.mkdir('_KOD_RESULTS')

    for ition, remove_index, check_index in product(prog.transitions(), chain([None], range(len(invs))), range(len(invs))):        
        kod_bench_with(_solver, ition, remove_index, check_index)

def z3_bench_with(
        solver: Solver,
        ition: DefinitionDecl,
        remove_index: Optional[int],
        check_index: int
        ) -> None:
    prog = syntax.the_program
    invs = [inv.expr for inv in prog.invs()] 
    pre_invs = [inv for counter, inv in enumerate(invs) if counter != remove_index]      
    class_name = get_class_name(utils.args.filename)
    file_name = f'{class_name}__{ition.name}__{remove_index}__{check_index}'
    lator = solver.get_translator(2)

    axioms = [a.expr for a in prog.axioms()]
    f = And(*axioms, *pre_invs, ition.as_twostate_formula(prog.scope), New(Not(invs[check_index])))

    with solver.new_frame():
        solver.add(lator.translate_expr(f))
        with open(file_name + '.smt2', 'w') as smt2_file:
            smt2_file.write(solver.z3solver.to_smt2())

def z3_benchmark(_solver: Solver) -> None:
    prog = syntax.the_program
    print(f'[{datetime.now()}] [PID={os.getpid()}] Starting benchmark on {os.path.basename(utils.args.filename)}')
    invs = [inv.expr for inv in prog.invs()]

    if not os.path.exists('_Z3_RESULTS'):
        os.mkdir('_Z3_RESULTS')

    for ition, remove_index, check_index in product(prog.transitions(), chain([None], range(len(invs))), range(len(invs))):        
        z3_bench_with(_solver, ition, remove_index, check_index)


def add_argparsers(subparsers: argparse._SubParsersAction) -> Iterable[argparse.ArgumentParser]:
    result : List[argparse.ArgumentParser] = []

    # forward_explore_inv
    s = subparsers.add_parser('kod-verify', help='Verify model using KodKod')
    s.set_defaults(main=kod_verify)
    result.append(s)

    s = subparsers.add_parser('kod-benchmark', help='Benchmark kodkod running time for finding instance by removing invariants one at a time')
    s.set_defaults(main=kod_benchmark)
    result.append(s)

    s = subparsers.add_parser('z3-benchmark', help='Benchmark kodkod running time for finding instance by removing invariants one at a time')
    s.set_defaults(main=z3_benchmark)
    result.append(s)

    for s in result:
        s.add_argument('--bound', type=int, help='Maximum bounds to use for bounded kodkod model.')
    
    return result
