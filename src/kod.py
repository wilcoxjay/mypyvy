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

class KodModel(object):

  def get_dependencies(self):
    return ["java.util.ArrayList",
            "java.util.List",
            "kodkod.ast.Formula",
            "kodkod.ast.Relation",
            "kodkod.ast.Variable",
            "kodkod.engine.Solution",
            "kodkod.engine.Solver",
            "kodkod.engine.satlab.SATFactory",
            "kodkod.instance.Bounds",
            "kodkod.instance.TupleFactory",
            "kodkod.instance.TupleSet",
            "kodkod.instance.Universe",
            ]

  '''
  dictionary of hardcoded (for now) relations and their respective arities
  '''
  def get_relations(self):
    # TODO: new relations? identify and append
    return {
      'client':1,
      'server':1,
      'id':1,
      'used':1,
      'new_used':1,
      'server_holds_lock':1,
      'new_server_holds_lock':1,
      'holds_lock':2,
      'new_holds_lock':2,
      'request_msg':3,
      'new_request_msg':3,
      'grant_msg':3,
      'new_grant_msg':3,
      'release_msg':3,
      'new_release_msg':3
    }
  
  def get_free_variables(self): # will probably take in some invariant/transition to give the respective free variables
    # will probably pass in some sort of INIT FLAG indication
    # Will have to "transform" from mypyvy/z3 syntax to get the variables
    # FOR NOW WE'LL JUST RETURN c1, c2, s1, s2, i1, i2
    return ['c1', 'c2', 's1', 's2', 'i1', 'i2']

  def get_init_conditions(self):
    # Will have to "transform" from mypyvy/z3 syntax -- Translating will be the interesting part
    # For now we'll just hard-encode them
    return [
      "s.in(server_holds_lock).forAll(s.oneOf(Server))",
      "used.no()",
      "holds_lock.no()",
      "request_msg.no()",
      "grant_msg.no()",
      "release_msg.no()",
    ]


  def constructor(self):
    lines = ["public _kodkod_model() {"]
    relations = self.get_relations()
    for rel in relations:
      lines.append(f'this.{rel} = Relation.nary(\"{rel}\", {str(relations[rel])});')
    lines.append("}\n")
    return lines
  
  def inits(self): # Will get from init statements
    lines = ["public Formula inits() {"]
    lines.extend([f'final Variable {v} = Variable.unary(\"{v}\");' for v in self.get_free_variables()]) 
    lines.append("final List<Formula> inits = new ArrayList<Formula>();")
    lines.extend([f'inits.add({i});' for i in self.get_init_conditions()])
    lines.append("return Formula.and(inits);\n}\n")
    return lines

  def get_bounds(self):
    lines = [
      'public Bounds bounds(int client, int server, int id) {',
      'final List<String> atoms = new ArrayList<String>(' + ' + '.join(f'_b{i}' for i in range(len(self.bounds))) + ');',
    ]
    # lines.extend(['for(int i = 0; i < _b' + str(i) + '; i++) {\natoms.add('])
    lines.append('}\n')
    return lines

  def check_inits(self):
    return [
      'public void checkInits(' + ', '.join(f'int _b{i}' for i in range(len(self.bounds))) + ') {',
      'final Solver solver = new Solver();',
      'solver.options().setSolver(SATFactory.MiniSat);',
      # this.inits() for NOW -- NEED TO CHANGE
      'final Solution sol = solver.solve(this.inits(), get_bounds(' + ', '.join(f'_b{i}' for i in range(len(self.bounds))) + '));',
      'System.out.println(sol);',
      '}\n'
      ]

  def check_transitions(self):
    return [
      'public void checkTransitions(' + ', '.join(f'int _b{i}' for i in range(len(self.bounds))) + ') {',
      'final Solver solver = new Solver();',
      'solver.options().setSolver(SATFactory.MiniSat);',
      '}\n'
      ]

  def main(self):
    lines = [
      'public static void main(String[] args) {',
      'final _kodkod_model model = new _kodkod_model();',
    ]
    lines.extend([f'final int _b{i} = Integer.parseInt(args[{i}]);' for i in range(len(self.bounds))])
    # lines.append('model.checkInits(' + *['_b' + str(i) for i in range(len(self.bounds))] + ');')
    lines.append('model.checkInits(' + ', '.join(f'_b{i}' for i in range(len(self.bounds))) + ');')
    lines.append('model.checkTransitions(' + ', '.join(f'_b{i}' for i in range(len(self.bounds))) + ');\n}')
    return lines

  def __init__(self, *bounds):
    if os.path.exists("_kodkod_model.java"):
      os.remove("_kodkod_model.java")
    self.file = open("_kodkod_model.java", "a")
    self.bounds = bounds

    # TODO
    self.class_methods_generators = [
      self.constructor,
      self.inits,
    #   self.declarations,
    #   self.get_invariants,
    #   self.get_transitions,
      self.get_bounds,
      self.check_inits,
      self.check_transitions,
      self.main,
    ]
  
  def __del__(self):
    self.file.close()

  # '''
  # header: method/class/header w/o '{', None if no header to be written with indentation ind
  # body: list of lines for the body to be written with indentation (ind + 1)
  # ind: indentation
  # * If a header is provided, encompasses body between an openning '{' and closing '}'
  # '''
  # def write_indented(self, header, body, ind):
  #   if header:
  #     self.file.write('  ' * ind + header + ' {\n')
  #   self.file.writelines([('  ' * (ind + 1)) + line + '\n' for line in body])
  #   if header:
  #     self.file.write('  ' * ind + '}\n')
  
  #   '''
  # body: list of lines for the body to be written with indentation (ind)
  # ind: indentation
  # * If a header is provided, encompasses body between an openning '{' and closing '}'
  # '''
  # def write_indented(self, lines, ind):
  #   if not lines:
  #     return

  #   self.file.write('  ' * ind + lines[0] + '\n')
  #   if line[0].strip()[-1] == '{':
  #     self.write_indented(lines[1:], ind + 1)
  #   else:
  #     self.write_indented(lines[1:], ind)

  def write_model(self):
    # write modules' imports
    self.file.writelines(f'import ' + module +';\n' for module in self.get_dependencies())
    self.file.write("public final class _kodkod_model {\n")
    self.file.writelines(f'private final Relation {rel};\n' for rel in self.get_relations().keys()) # write relations
    for generator in self.class_methods_generators:
      self.file.writelines(f'{line}\n' for line in generator())
    self.file.write("}")
  
def to_kodkod(e: Expr) -> str:
  if isinstace(e, QuantifierExpr) and e.quant == 'FORALL':
    return to_kodkod(e.body) + '.forAll(...)'


def kod_verify(_solver: Solver) -> str:
    '''
    '''
    prog = syntax.the_program
    print(f'\n[{datetime.now()}] [PID={os.getpid()}] Starting kod_verify\n')

    inits = tuple(chain(*(as_clauses(init.expr) for init in prog.inits()))) # convert to CNF
    safety = [inv.expr for inv in prog.invs() if inv.is_safety]
    invs = [inv.expr for inv in prog.invs() if not inv.is_safety]

    for i, p in enumerate(invs):
      print(f'invariant {i}: {p}')
    

    model = KodModel(3, 3, 3)
    model.write_model()   


def add_argparsers(subparsers: argparse._SubParsersAction) -> Iterable[argparse.ArgumentParser]:
    result : List[argparse.ArgumentParser] = []

    # forward_explore_inv
    s = subparsers.add_parser('kod-verify', help='Verify invariants using KodKod')
    s.set_defaults(main=kod_verify)
    result.append(s)

    for s in result:
        s.add_argument('--scope', type=int, help='')

    return result
