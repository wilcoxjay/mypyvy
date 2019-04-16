"""
This file contains code for the Primal Dual research project
"""

from __future__ import annotations

from mypyvy import *


def reachability_tree(s: Solver, prog: Program) -> None:
    print('hey oded and kartik')

    models: List[Model] = []

    # somehow, we got this list of formulas
    l: List[Expr]

    inits = [init.expr for init in prog.inits()]
    res = check_two_state_implication_all_transitions(s, prog, inits, l[0])
    if res is not None:
        z3m, ition = res
        models.append(Model(prog, z3m, s, [KEY_NEW, KEY_OLD]))

    for e in l[1:]:
        res = check_two_state_implication_all_transitions(s, prog, [models[-1].as_onestate_formula(i=0)], e)
        if res is not None:
            z3m, ition = res
            models.append(Model(prog, z3m, s, [KEY_NEW, KEY_OLD]))


def pd_add_argparsers(subparsers: argparse._SubParsersAction) -> List[argparse.ArgumentParser]:
    reachability_tree_subparser = subparsers.add_parser('reachability-tree', help='TODO write help')
    reachability_tree_subparser.set_defaults(main=reachability_tree)
    return [reachability_tree_subparser]
