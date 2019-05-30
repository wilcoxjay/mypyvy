#!/usr/bin/env python3.7

from __future__ import annotations
import argparse
from datetime import datetime
import logging
import sys
from typing import List, Any, Optional, cast
import z3

import logic
from logic import Solver, KEY_NEW, KEY_OLD, KEY_ONE
import parser
import syntax
from syntax import Expr, Program, Scope, InvariantDecl, AutomatonDecl
import updr
import utils

import pd

def get_safety(prog: Program) -> List[Expr]:
    if utils.args.safety is not None:
        the_inv: Optional[InvariantDecl] = None
        for inv in prog.invs():
            if inv.name == utils.args.safety:
                the_inv = inv
        if the_inv is None:
            raise Exception('No safety invariant named %s' % utils.args.safety)
        safety: List[Expr] = [the_inv.expr]
    else:
        safety = [s.expr for s in prog.safeties()]

    return safety


@utils.log_start_end_xml(utils.logger, logging.INFO)
@utils.log_start_end_time(utils.logger, logging.INFO)
def do_updr(s: Solver, prog: Program) -> None:
    if utils.args.use_z3_unsat_cores:
        z3.set_param('smt.core.minimize', True)

    logic.check_init(s, prog, safety_only=True)

    fs = updr.Frames(s, prog)
    fs.search()

def debug_tokens(filename: str) -> None:
    l = parser.get_lexer()

    with open(filename) as f:
        l.input(f.read())

    while True:
        tok = l.token()
        if not tok:
            break      # No more input
        utils.logger.always_print(str(tok))


def check_automaton_init(s: Solver, prog: Program, a: AutomatonDecl) -> None:
    utils.logger.always_print('checking automaton init:')

    t = s.get_translator(KEY_ONE)

    init_decl = a.the_init()
    assert init_decl is not None  # checked by resolver
    init_phase = prog.scope.get_phase(init_decl.phase)
    assert init_phase is not None  # checked by resolver

    with s:
        for init in prog.inits():
            s.add(t.translate_expr(init.expr))

        for inv in init_phase.invs():
            with s:
                s.add(z3.Not(t.translate_expr(inv.expr)))

                if inv.tok is not None:
                    msg = ' on line %d' % inv.tok.lineno
                else:
                    msg = ''
                utils.logger.always_print('  implies phase invariant%s... ' % msg, end='')
                sys.stdout.flush()

                logic.check_unsat([(inv.tok, 'phase invariant%s may not hold in initial state' % msg)], s, prog, [KEY_ONE])

def check_automaton_edge_covering(s: Solver, prog: Program, a: AutomatonDecl) -> None:
    utils.logger.always_print('checking automaton edge covering:')

    t = s.get_translator(KEY_NEW, KEY_OLD)

    for phase in a.phases():
        utils.logger.always_print('  checking phase %s:' % phase.name)
        with s:
            for inv in phase.invs():
                s.add(t.translate_expr(inv.expr, old=True))

            for trans in prog.transitions():
                if any(delta.transition == trans.name and delta.precond is None for delta in phase.transitions()):
                    utils.logger.always_print('    transition %s is covered trivially.' % trans.name)
                    continue

                utils.logger.always_print('    checking transition %s is covered... ' % trans.name, end='')

                with s:
                    s.add(t.translate_transition(trans))
                    s.add(z3.And(*(z3.Not(t.translate_precond_of_transition(delta.precond, trans))
                                   for delta in phase.transitions() if trans.name == delta.transition)))

                    logic.check_unsat([(phase.tok, 'transition %s is not covered by this phase' %
                                        (trans.name, )),
                                       (trans.tok, 'this transition misses transitions from phase %s' % (phase.name,))],
                                      s, prog, [KEY_OLD, KEY_NEW])


def check_automaton_inductiveness(s: Solver, prog: Program, a: AutomatonDecl) -> None:
    utils.logger.always_print('checking automaton inductiveness:')

    t = s.get_translator(KEY_NEW, KEY_OLD)

    for phase in a.phases():
        utils.logger.always_print('  checking phase %s:' % phase.name)

        with s:
            for inv in phase.invs():
                s.add(t.translate_expr(inv.expr, old=True))

            for delta in phase.transitions():
                trans = prog.scope.get_definition(delta.transition)
                assert trans is not None
                precond = delta.precond
                target = prog.scope.get_phase(delta.target) if delta.target is not None else phase
                assert target is not None

                trans_pretty = '(%s, %s)' % (trans.name, str(precond) if (precond is not None) else 'true')
                utils.logger.always_print('    checking transition: %s' % trans_pretty)

                with s:
                    s.add(t.translate_transition(trans, precond=precond))
                    for inv in target.invs():
                        with s:
                            s.add(z3.Not(t.translate_expr(inv.expr)))

                            if inv.tok is not None:
                                msg = ' on line %d' % inv.tok.lineno
                            else:
                                msg = ''
                            utils.logger.always_print('      preserves invariant%s... ' % msg, end='')
                            sys.stdout.flush()

                            logic.check_unsat([(inv.tok, 'invariant%s may not be preserved by transition %s in phase %s' %
                                                (msg, trans_pretty, phase.name)),
                                               (delta.tok, 'this transition may not preserve invariant%s' % (msg,))],
                                              s, prog, [KEY_OLD, KEY_NEW])

@utils.log_start_end_time(utils.logger, logging.INFO)
def verify(s: Solver, prog: Program) -> None:
    old_count = utils.error_count
    a = prog.the_automaton()
    if a is None:
        if utils.args.automaton == 'only':
            utils.print_error_and_exit(None, "--automaton='only' requires the file to declare an automaton")
    elif utils.args.automaton != 'no':
        check_automaton_full(s, prog, a)

    if utils.args.automaton != 'only':
        logic.check_init(s, prog)
        logic.check_transitions(s, prog)

    if utils.error_count == old_count:
        utils.logger.always_print('all ok!')
    else:
        utils.logger.always_print('program has errors.')

def check_automaton_full(s: Solver, prog: Program, a: AutomatonDecl) -> None:
    check_automaton_init(s, prog, a)
    check_automaton_inductiveness(s, prog, a)
    check_automaton_edge_covering(s, prog, a)

@utils.log_start_end_time(utils.logger)
def bmc(s: Solver, prog: Program) -> None:
    safety = syntax.And(*get_safety(prog))

    n = utils.args.depth

    utils.logger.always_print('bmc checking the following property to depth %d' % n)
    utils.logger.always_print('  ' + str(safety))

    start = datetime.now()

    logic.check_bmc(s, prog, safety, n)


@utils.log_start_end_time(utils.logger)
def theorem(s: Solver, prog: Program) -> None:
    utils.logger.always_print('checking theorems:')

    for th in prog.theorems():
        if th.twostate:
            keys = [KEY_OLD, KEY_NEW]
        else:
            keys = [KEY_ONE]

        t = s.get_translator(*keys)

        if th.name is not None:
            msg = ' ' + th.name
        elif th.tok is not None:
            msg = ' on line %d' % th.tok.lineno
        else:
            msg = ''

        utils.logger.always_print(' theorem%s... ' % msg, end='')
        sys.stdout.flush()

        with s:
            s.add(z3.Not(t.translate_expr(th.expr)))

            logic.check_unsat([(th.tok, 'theorem%s may not hold' % msg)], s, prog, keys)

def nop(s: Solver, prog: Program) -> None:
    pass

def ipython(s:Solver, prog: Program) -> None:
    import IPython  # type: ignore
    #IPython.embed()
    IPython.start_ipython(argv=[],user_ns=dict(locals()))

def translate_transition_call(s: Solver, prog: Program, key: str, key_old: str, c: syntax.TransitionCall) -> z3.ExprRef:
    ition = prog.scope.get_definition(c.target)
    assert ition is not None
    lator = s.get_translator(key, key_old)
    bs = lator.bind(ition.binder)
    qs: List[Optional[z3.ExprRef]] = [b for b in bs]
    if c.args is not None:
        for j, a in enumerate(c.args):
            if isinstance(a, Expr):
                bs[j] = lator.translate_expr(a)
                qs[j] = None
            else:
                assert isinstance(a, syntax.Star)
                pass
    qs1 = [q for q in qs if q is not None]
    with lator.scope.in_scope(ition.binder, bs):
        body = lator.translate_transition_body(ition)
    if len(qs1) > 0:
        return z3.Exists(qs1, body)
    else:
        return body

def trace(s: Solver, prog: Program) -> None:
    if len(list(prog.traces())) > 0:
        utils.logger.always_print('finding traces:')

    for trace in prog.traces():
        n_states = len(list(trace.transitions())) + 1
        print('%s states' % (n_states,))

        keys = ['state%2d' % i for i in range(n_states)]

        for k in keys:
            s.get_translator(k)  # initialize all the keys before pushing a solver stack frame

        with s:
            lator = s.get_translator(keys[0])
            if len(trace.components) > 0 and not isinstance(trace.components[0], syntax.AssertDecl):
                for init in prog.inits():
                    s.add(lator.translate_expr(init.expr))

            i = 0
            for c in trace.components:
                if isinstance(c, syntax.AssertDecl):
                    if c.expr is None:
                        if i != 0:
                            utils.print_error_and_exit(c.tok, 'assert init is only allowed in the first state')
                        for init in prog.inits():
                            s.add(s.get_translator(keys[i]).translate_expr(init.expr))
                    else:
                        s.add(s.get_translator(keys[i]).translate_expr(c.expr))
                else:
                    te: syntax.TransitionExpr = c.transition
                    if isinstance(te, syntax.AnyTransition):
                        logic.assert_any_transition(s, prog, str(i), keys[i+1], keys[i], allow_stutter=True)
                    else:
                        l = []
                        for call in te.calls:
                            tid = z3.Bool(logic.get_transition_indicator(str(i), call.target))
                            l.append(tid)
                            s.add(tid == translate_transition_call(s, prog, keys[i+1], keys[i], call))
                        s.add(z3.Or(*l))

                    i += 1

            res = logic.check_unsat([], s, prog, keys)
            if (res == z3.sat) != trace.sat:
                utils.print_error(trace.tok, 'trace declared %s but was %s!' % ('sat' if trace.sat else 'unsat', res))


def parse_args(args: List[str]) -> utils.MypyvyArgs:
    argparser = argparse.ArgumentParser()

    subparsers = argparser.add_subparsers(title='subcommands')
    all_subparsers = []

    verify_subparser = subparsers.add_parser('verify', help='verify that the invariants are inductive')
    verify_subparser.set_defaults(main=verify)
    all_subparsers.append(verify_subparser)

    updr_subparser = subparsers.add_parser('updr', help='search for a strengthening that proves the invariant named by the --safety=NAME flag')
    updr_subparser.set_defaults(main=do_updr)
    all_subparsers.append(updr_subparser)

    bmc_subparser = subparsers.add_parser('bmc', help='bounded model check to depth given by the --depth=DEPTH flag for property given by the --safety=NAME flag')
    bmc_subparser.set_defaults(main=bmc)
    all_subparsers.append(bmc_subparser)

    theorem_subparser = subparsers.add_parser('theorem', help='check state-independent theorems about the background axioms of a model')
    theorem_subparser.set_defaults(main=theorem)
    all_subparsers.append(theorem_subparser)

    trace_subparser = subparsers.add_parser('trace', help='search for concrete executions that satisfy query described by the file\'s trace declaration')
    trace_subparser.set_defaults(main=trace)
    all_subparsers.append(trace_subparser)

    generate_parser_subparser = subparsers.add_parser('generate-parser', help='internal command used by benchmarking infrastructure to avoid certain race conditions')
    generate_parser_subparser.set_defaults(main=nop)  # parser is generated implicitly by main when it parses the program
    all_subparsers.append(generate_parser_subparser)

    typecheck_subparser = subparsers.add_parser('typecheck', help='typecheck the file, report any errors, and exit')
    typecheck_subparser.set_defaults(main=nop)  # program is always typechecked; no further action required
    all_subparsers.append(typecheck_subparser)

    all_subparsers += pd.add_argparsers(subparsers)

    for s in all_subparsers:
        s.add_argument('--forbid-parser-rebuild', action=utils.YesNoAction, default=False,
                       help='force loading parser from disk (helps when running mypyvy from multiple processes)')
        s.add_argument('--log', default='warning', choices=['error', 'warning', 'info', 'debug'],
                       help='logging level')
        s.add_argument('--log-time', action=utils.YesNoAction, default=False,
                       help='make each log message include current time')
        s.add_argument('--log-xml', action=utils.YesNoAction, default=False,
                       help='log in XML format')
        s.add_argument('--seed', type=int, default=0, help="value for z3's smt.random_seed")
        s.add_argument('--print-program-repr', action=utils.YesNoAction, default=False,
                       help='print a machine-readable representation of the program after parsing')
        s.add_argument('--print-program', action=utils.YesNoAction, default=False,
                       help='print the program after parsing')
        s.add_argument('--key-prefix',
                       help='additional string to use in front of names sent to z3')
        s.add_argument('--minimize-models', action=utils.YesNoAction, default=True,
                       help='search for models with minimal cardinality')
        s.add_argument('--timeout', type=int, default=None,
                       help='z3 timeout (milliseconds)')
        s.add_argument('--exit-on-error', action=utils.YesNoAction, default=False,
                       help='exit after reporting first error')
        s.add_argument('--ipython', action=utils.YesNoAction, default=False,
                       help='run IPython with s and prog at the end')
        s.add_argument('--error-filename-basename', action=utils.YesNoAction, default=False,
                       help='print only the basename of the input file in error messages')
        s.add_argument('--query-time', action=utils.YesNoAction, default=True,
                       help='report how long various z3 queries take')
        s.add_argument('--print-counterexample', action=utils.YesNoAction, default=True,
                       help='print counterexamples')
        s.add_argument('--print-cmdline', action=utils.YesNoAction, default=True,
                       help='print the command line passed to mypyvy')

        # for diagrams:
        s.add_argument('--simplify-diagram', action=utils.YesNoAction,
                       default=(s is updr_subparser),
                       default_description='yes for updr, else no',
                       help='in diagram generation, substitute existentially quantified variables that are equal to constants')


    updr_subparser.add_argument('--use-z3-unsat-cores', action=utils.YesNoAction, default=True,
                                help='generalize diagrams using brute force instead of unsat cores')
    updr_subparser.add_argument('--smoke-test', action=utils.YesNoAction, default=False,
                                help='(for debugging mypyvy itself) run bmc to confirm every conjunct added to a frame')
    updr_subparser.add_argument('--assert-inductive-trace', action=utils.YesNoAction, default=False,
                                help='(for debugging mypyvy itself) check that frames are always inductive')

    updr_subparser.add_argument('--sketch', action=utils.YesNoAction, default=False,
                                help='use sketched invariants as additional safety (currently only in automaton)')

    updr_subparser.add_argument('--automaton', action=utils.YesNoAction, default=False,
                                help='whether to run vanilla UPDR or phase UPDR')
    updr_subparser.add_argument('--block-may-cexs', action=utils.YesNoAction, default=False,
                                help="treat failures to push as additional proof obligations")
    updr_subparser.add_argument('--push-frame-zero', default='if_trivial', choices=['if_trivial', 'always', 'never'],
                                help="push lemmas from the initial frame: always/never/if_trivial, the latter is when there is more than one phase")

    verify_subparser.add_argument('--automaton', default='yes', choices=['yes', 'no', 'only'],
                                  help="whether to use phase automata during verification. by default ('yes'), both non-automaton "
                                  "and automaton proofs are checked. 'no' means ignore automaton proofs. "
                                  "'only' means ignore non-automaton proofs.")
    verify_subparser.add_argument('--check-transition', default=None, nargs='+',
                                  help="when verifying inductiveness, check only these transitions")
    verify_subparser.add_argument('--check-invariant', default=None, nargs='+',
                                  help="when verifying inductiveness, check only these invariants")

    bmc_subparser.add_argument('--safety', help='property to check')
    bmc_subparser.add_argument('--depth', type=int, default=3, metavar='N',
                               help='number of steps to check')

    argparser.add_argument('filename')

    return cast(utils.MypyvyArgs, argparser.parse_args(args))

class MyFormatter(logging.Formatter):
    def __init__(self, fmt: str) -> None:
        super().__init__(fmt='%(levelname)s ' + fmt)
        self.withoutlevel = logging.Formatter(fmt='%(message)s')
        self.start = datetime.now()

    def format(self, record: Any) -> str:
        if record.levelno == utils.MyLogger.ALWAYS_PRINT:
            return self.withoutlevel.format(record)
        else:
            return super().format(record)

    def formatTime(self, record: Any, datefmt: Optional[str]=None) -> str:
        return str((datetime.now() - self.start).total_seconds())

def parse_program(input: str, force_rebuild: bool=False, filename: Optional[str]=None) -> Program:
    l = parser.get_lexer()
    p = parser.get_parser(forbid_rebuild=force_rebuild)
    return p.parse(input=input, lexer=l, filename=filename)

def main() -> None:
    utils.args = parse_args(sys.argv[1:])

    if utils.args.log_xml:
        fmt = '%(message)s'
    elif utils.args.log_time:
        fmt = '%(asctime)s %(filename)s:%(lineno)d: %(message)s'
    else:
        fmt = '%(filename)s:%(lineno)d: %(message)s'

    utils.logger.setLevel(getattr(logging, utils.args.log.upper(), None))
    handler = logging.StreamHandler(stream=sys.stdout)
    handler.terminator = ''
    handler.setFormatter(MyFormatter(fmt))
    logging.root.addHandler(handler)
    # utils.logger.addHandler(handler)

    if utils.args.key_prefix is not None:
        global KEY_ONE
        global KEY_NEW
        global KEY_OLD

        KEY_ONE = utils.args.key_prefix + '_' + KEY_ONE
        KEY_NEW = utils.args.key_prefix + '_' + KEY_NEW
        KEY_OLD = utils.args.key_prefix + '_' + KEY_OLD

    with utils.LogTag(utils.logger, 'main', lvl=logging.INFO):
        if utils.args.print_cmdline:
            utils.logger.info(' '.join([sys.executable] + sys.argv))
            utils.logger.info('Running mypyvy with the following options:')
            for k, v in sorted(vars(utils.args).items()):
                utils.logger.info(f'    {k} = {v!r}')

        utils.logger.info('setting seed to %d' % utils.args.seed)
        z3.set_param('smt.random_seed', utils.args.seed)

        # utils.logger.info('enable z3 macro finder')
        # z3.set_param('smt.macro_finder', True)

        if utils.args.timeout is not None:
            utils.logger.info('setting z3 timeout to %s' % utils.args.timeout)
            z3.set_param('timeout', utils.args.timeout)

        pre_parse_error_count = utils.error_count

        with open(utils.args.filename) as f:
            prog = parse_program(f.read(), force_rebuild=utils.args.forbid_parser_rebuild, filename=utils.args.filename)

        if utils.error_count > pre_parse_error_count:
            utils.logger.always_print('program has syntax errors.')
            sys.exit(1)

        if utils.args.print_program_repr:
            utils.logger.always_print(repr(prog))
        if utils.args.print_program:
            utils.logger.always_print(str(prog))

        pre_resolve_error_count = utils.error_count

        prog.resolve()
        if utils.error_count > pre_resolve_error_count:
            utils.logger.always_print('program has resolution errors.')
            sys.exit(1)

        s = Solver(prog)

        utils.args.main(s, prog)

        utils.logger.info('total number of queries: %s' % s.nqueries)

        if utils.args.ipython:
            ipython(s, prog)

    sys.exit(1 if utils.error_count > 0 else 0)


if __name__ == '__main__':
    main()
