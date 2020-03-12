import logic
from logic import Solver, Diagram, Trace, KEY_NEW, KEY_OLD
import syntax
from syntax import Expr
import utils

import z3
import argparse
import logging

from typing import Iterable, List, Tuple, Optional, Sequence

def get_cti(s: Solver, candidate: Expr) -> Optional[Tuple[Diagram, Diagram]]:
    res = logic.check_two_state_implication_all_transitions(s, [candidate], candidate, minimize=True)
    if res is None:
        return None

    z3m: z3.ModelRef = res[0]
    mod = Trace.from_z3((KEY_OLD, KEY_NEW), z3m)
    return (mod.as_diagram(i=0), mod.as_diagram(i=1))

def generalize_cex_omission_checker(s: Solver, diag_to_exclude: Diagram, depth: int) -> bool:
    res = logic.my_temp_bmc(s, syntax.Not(diag_to_exclude.to_ast()), depth)
    utils.logger.info("bmc res for %s: %s" % (diag_to_exclude, res))
    excludes_bounded_reachable_states = (res != None)
    return not excludes_bounded_reachable_states

def itp_gen(s: Solver) -> None:
    k = 4

    prog = syntax.the_program
    safety = syntax.And(*(inv.expr for inv in prog.invs() if inv.is_safety))
    inits = [init.expr for init in prog.inits()]

    utils.logger.info("initial state: %s" % str(inits))
    utils.logger.info("proving safety property: %s" % safety)

    candidate = [safety]
    while True:
        cti = get_cti(s, syntax.And(*candidate))
        if cti is None:
            break

        utils.args.smoke_test = False # TODO: uber hack, could be made better but why should it...

        pre_diag = cti[0]

        uc = s.unsat_core()

        pre_diag.generalize_general(s,
                                    lambda diag: generalize_cex_omission_checker(s, diag, k),
                                    k)
        #                     self[j - 1],
        #                     self.automaton.transitions_to_grouped_by_src(p),
        #                     True,
        #                     k)

        e = syntax.Not(pre_diag.to_ast())

        utils.logger.info('adding new clause to the invariant: %s' % str(e))
        candidate.append(e)

    res = logic.check_implication(s, inits, candidate)
    if res is not None:
        utils.logger.always_print("Failure: candidate %s excludes initial states" % str(candidate))
    else:
        utils.logger.always_print("Success! Inductive invariant:")
        for clause in candidate:
            utils.logger.always_print(str(clause))

def add_argparsers(subparsers: argparse._SubParsersAction) -> Iterable[argparse.ArgumentParser]:
    result : List[argparse.ArgumentParser] = []

    s = subparsers.add_parser('itp-literal', help='experimental inference 1')
    s.set_defaults(main=itp_gen)
    result.append(s)

    return result