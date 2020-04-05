import logic
from logic import Solver, Diagram, Trace, KEY_NEW, KEY_OLD
import syntax
from syntax import Expr
import utils
import copy

import z3
import argparse

from typing import Iterable, List, Tuple, Optional, Set

def get_cti(s: Solver, candidate: Expr) -> Optional[Tuple[Diagram, Diagram]]:
    res = logic.check_two_state_implication_all_transitions(s, [candidate], candidate, minimize=True)
    if res is None:
        return None

    z3m: z3.ModelRef = res[0]
    mod = Trace.from_z3((KEY_OLD, KEY_NEW), z3m)
    return (mod.as_diagram(index=0), mod.as_diagram(index=1))

def bmc_upto_bound(s: Solver, post: Expr, bound: int, preconds: Optional[Iterable[Expr]]=None) -> Optional[logic.Trace]:
    for k in range(0, bound + 1):
        if (m := logic.check_bmc(s, post, k, preconds=preconds)) is not None:
            return m
    return None

def itp_gen(s: Solver) -> None:
    k = 4

    prog = syntax.the_program
    safety = syntax.And(*(inv.expr for inv in prog.invs() if inv.is_safety))
    inits = [init.expr for init in prog.inits()]

    utils.logger.info("initial state: %s" % str(inits))
    utils.logger.info("proving safety property: %s" % safety)

    candidate = [safety]

    # with logic.BoundedReachabilityCheck(s, syntax.the_program, k) as bmc_checker:
    while True:
        cti = get_cti(s, syntax.And(*candidate))
        if cti is None:
            break

        pre_diag = cti[0]

        # core = bmc_checker.unsat_core(pre_diag)
        # if core is None:
        #     utils.logger.always_print("Failure: attempted to exclude reachable state, a pre-state of %s" %
        #                               ' & '.join(str(clause) for clause in candidate))
        #     assert False
        #
        # pre_diag.minimize_from_core(core)

        pre_diag.generalize(s, lambda diag: bmc_upto_bound(s, syntax.Not(diag.to_ast()), k) is None)

        e = syntax.Not(pre_diag.to_ast())

        utils.logger.info('adding new clause to the invariant: %s' % str(e))
        candidate.append(e)

    if logic.check_implication(s, inits, candidate) is not None:
        utils.logger.always_print("Failure: candidate %s excludes initial states" %
                                  ' & '.join(str(clause) for clause in candidate))
    else:
        utils.logger.always_print("Success! Inductive invariant:")
        for clause in candidate:
            utils.logger.always_print(str(clause))

def valid_in_initial_frame(s: Solver, inits: List[Expr], e: Expr) -> bool:
    return logic.check_implication(s, inits, [e], minimize=False) is None

def brat(s: Solver) -> None:
    k = 6

    prog = syntax.the_program
    safety = syntax.And(*(inv.expr for inv in prog.invs() if inv.is_safety))
    inits = [init.expr for init in prog.inits()]

    utils.logger.info("initial state: %s" % str(inits))
    utils.logger.info("proving safety property: %s" % safety)

    current_frame = inits
    prev_frame: List[Expr] = [syntax.FalseExpr]

    bad_cache: Set[Diagram] = set()

    while logic.check_implication(s, current_frame, prev_frame, minimize=False) is not None:
        prev_frame = current_frame
        current_frame = brat_new_frame(s, prev_frame, k, inits, safety, bad_cache)
        utils.logger.info("Frame:")
        for c in current_frame:
            utils.logger.info(str(c))

    utils.logger.always_print("Success! Inductive invariant:")
    for clause in current_frame:
        utils.logger.always_print(str(clause))
    verify_inductive_invariant(s, current_frame)


def brat_new_frame(s: Solver, prev_frame: List[Expr],
                   bound: int, inits: List[Expr], safety: Expr,
                   bad_cache: Set[Diagram]) -> List[Expr]:
    current_frame: List[Expr] = [syntax.TrueExpr]

    for bad_model in bad_cache:
        if logic.check_implication(s, current_frame, [syntax.Not(bad_model.to_ast())]) is None:
            continue
        current_frame.append(post_image_prime_consequence(s, prev_frame, inits, bad_model))

    while (bad_trace := bmc_upto_bound(s, safety, bound, preconds=current_frame)) is not None:
        bad_model = bad_trace.as_diagram(0)
        bad_cache.add(bad_model)
        current_frame.append(post_image_prime_consequence(s, prev_frame, inits, bad_model))

    return current_frame


def post_image_prime_consequence(s: Solver, prev_frame: List[Expr], inits: List[Expr], bad_model: Diagram) -> Expr:
    # TODO: duplicated from updr
    def prev_frame_constraint(diag: Diagram) -> bool:
        return (
                logic.check_two_state_implication_all_transitions(
                    s, prev_frame, syntax.Not(diag.to_ast()), minimize=False
                ) is None
                and valid_in_initial_frame(s, inits, syntax.Not(diag.to_ast()))
        )

    bad_model_copy = copy.deepcopy(bad_model)
    bad_model_copy.generalize(s, prev_frame_constraint)

    return syntax.Not(bad_model_copy.to_ast())


def verify_inductive_invariant(s: Solver, inv: List[Expr]) -> None:
    prog = syntax.the_program
    inits = [init.expr for init in prog.inits()]
    safeties = [inv.expr for inv in prog.invs() if inv.is_safety]

    assert logic.check_implication(s, inits, inv) is None
    assert logic.check_implication(s, inv, safeties) is None
    assert logic.check_implication(s, inv, inv) is None


def add_argparsers(subparsers: argparse._SubParsersAction) -> Iterable[argparse.ArgumentParser]:
    result: List[argparse.ArgumentParser] = []

    s = subparsers.add_parser('itp-literal', help='experimental inference 1')
    s.set_defaults(main=itp_gen)
    result.append(s)

    s = subparsers.add_parser('brat', help='experimental inference 2')
    s.set_defaults(main=brat)
    result.append(s)

    return result
