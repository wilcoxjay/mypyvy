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

def bmc_upto_bound(s: Solver, post: Expr, bound: int, preconds: Optional[Iterable[Expr]]=None,
                   minimize: Optional[bool]=None) -> Optional[logic.Trace]:
    for k in range(0, bound + 1):
        if (m := logic.check_bmc(s, post, k, preconds=preconds, minimize=minimize)) is not None:
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
    k = utils.args.depth

    prog = syntax.the_program
    safety = syntax.And(*(inv.expr for inv in prog.invs() if inv.is_safety))
    inits = [init.expr for init in prog.inits()]

    utils.logger.info("initial state: %s" % str(inits))
    utils.logger.info("proving safety property: %s" % safety)

    current_frame = inits
    prev_frame: List[Expr] = [syntax.FalseExpr]

    bad_cache: Set[Diagram] = set()

    idx = 0
    while logic.check_implication(s, current_frame, prev_frame, minimize=False) is not None:
        idx += 1
        prev_frame = current_frame
        if not utils.args.decrease_depth:
            current_depth = k
        else:
            current_depth = k - idx + 1
            if current_depth <= 0:
                assert False, "exhaused bmc depth: becoming non-positive"

        current_frame = brat_next_frame(s, prev_frame, current_depth, inits, safety, bad_cache, utils.args.minimize_models)
        utils.logger.info("Frame: %d" % idx)
        for c in current_frame:
            utils.logger.info(str(c))

    utils.logger.always_print("Success! Inductive invariant:")
    for clause in current_frame:
        utils.logger.always_print(str(clause))
    verify_inductive_invariant(s, current_frame)


def brat_next_frame(s: Solver, prev_frame: List[Expr],
                   bound: int, inits: List[Expr], safety: Expr,
                   bad_cache: Set[Diagram],
                   minimize: bool) -> List[Expr]:
    current_frame: List[Expr] = new_frame(s, prev_frame)

    for bad_model in bad_cache:
        if logic.check_implication(s, current_frame, [syntax.Not(bad_model.to_ast())]) is None:
            continue
        current_frame.append(post_image_prime_consequence(s, prev_frame, inits, bad_model))

    while (bad_trace := bmc_upto_bound(s, safety, bound, preconds=current_frame, minimize=minimize)) is not None:
        bad_model = bad_trace.as_diagram(0)
        bad_cache.add(bad_model)
        current_frame.append(post_image_prime_consequence(s, prev_frame, inits, bad_model))

    return current_frame


def new_frame(s: Solver, prev_frame: List[Expr]) -> List[Expr]:
    if not utils.args.push:
        return [syntax.TrueExpr]

    current_frame = []

    for c in prev_frame:
        if c == syntax.FalseExpr:
            continue
        if logic.check_two_state_implication_all_transitions(s, prev_frame, c, minimize=False) is None:
            current_frame.append(c)

    if not current_frame:
        current_frame = [syntax.TrueExpr]
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

    # TODO: unsat core first
    bad_model_copy = copy.deepcopy(bad_model)
    bad_model_copy.generalize(s, prev_frame_constraint)

    return syntax.Not(bad_model_copy.to_ast())

def oneshot_compute_inv(s: Solver,
                        bound: int,
                        inits: List[Expr], safety: Expr,
                        minimize: bool) -> List[Expr]:
    current_frame: List[Expr] = [syntax.TrueExpr]

    while (bad_trace := bmc_upto_bound(s, safety, bound, preconds=current_frame, minimize=minimize)) is not None:
        bad_model = bad_trace.as_diagram(0)
        current_frame.append(bmc_prime_consequence(s, utils.args.forward_depth, inits, bad_model))

    return current_frame

def bmc_prime_consequence(s: Solver, bound: int, inits: List[Expr], bad_model: Diagram) -> Expr:
    def bmc_constraint(diag: Diagram) -> bool:
        return logic.check_bmc(s, syntax.Not(diag.to_ast()), bound, preconds=inits) is None

    bad_model_copy = copy.deepcopy(bad_model)
    bad_model_copy.generalize(s, bmc_constraint)

    return syntax.Not(bad_model_copy.to_ast())

def oneshot(s: Solver) -> None:
    prog = syntax.the_program
    safety = syntax.And(*(inv.expr for inv in prog.invs() if inv.is_safety))
    inits = [init.expr for init in prog.inits()]

    utils.logger.info("initial state: %s" % str(inits))
    utils.logger.info("proving safety property: %s" % safety)

    candidate = oneshot_compute_inv(s, utils.args.depth, inits, safety, minimize=True)
    utils.logger.always_print("Got candidate:")
    for clause in candidate:
        utils.logger.always_print(str(clause))
    verify_inductive_invariant(s, candidate)

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

    brat_subparser = subparsers.add_parser('brat', help='experimental inference 2')
    brat_subparser.set_defaults(main=brat)
    result.append(brat_subparser)

    # TODO: remove default for depth
    brat_subparser.add_argument('--depth', type=int, default=6, metavar='N',
                                help='number of steps in backwards exploration')
    brat_subparser.add_argument('--push', action=utils.YesNoAction, default=True,
                                help='new frame begins with pushing from previous frame')
    brat_subparser.add_argument('--decrease-depth', action=utils.YesNoAction, default=False,
                                help='BMC bound decreased as frames increase (similar to PDR with backward-reach cache)')


    oneshot_subparser = subparsers.add_parser('oneshot', help='experimental inference 3')
    oneshot_subparser.set_defaults(main=oneshot)
    result.append(oneshot_subparser)
    oneshot_subparser.add_argument('--depth', type=int, default=6, metavar='N',
                                help='number of steps in backwards exploration')
    oneshot_subparser.add_argument('--forward-depth', type=int, default=4, metavar='N',
                                help='number of steps in forwards exploration')

    return result
