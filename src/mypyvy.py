#!/usr/bin/env python3.8

from __future__ import annotations
import argparse
from datetime import datetime
import json
import logging
import sys
from typing import Any, cast, Dict, List, Optional, Tuple, TypeVar, Callable, Union, Sequence, Set
import z3
import resource

import logic
from logic import Solver, KEY_NEW, KEY_OLD, KEY_ONE
import parser
import syntax
from syntax import Expr, Program, InvariantDecl
import updr
import utils
import relaxed_traces
from trace import bmc_trace

import pd
import rethink
import sep

T = TypeVar('T')

def get_safety() -> List[Expr]:
    prog = syntax.the_program
    safety: List[Expr]
    if utils.args.safety is not None:
        the_inv: Optional[InvariantDecl] = None
        for inv in prog.invs():
            if inv.name == utils.args.safety:
                the_inv = inv
        if the_inv is not None:
            safety = [the_inv.expr]
        else:
            try:
                oldcount = utils.error_count
                e = syntax.close_free_vars(parser.parse_expr(utils.args.safety))
                with prog.scope.n_states(1):
                    e.resolve(prog.scope, syntax.BoolSort)
                assert oldcount == utils.error_count, 'errors in parsing or typechecking'
                safety = [e]
            except Exception as e:
                print(e)
                utils.print_error_and_exit(None,
                                           f'--safety received string "{utils.args.safety}", '
                                           'which is neither the name of an invariant/safety property '
                                           'nor does it parse and typecheck as an expression')
    else:
        safety = [s.expr for s in prog.safeties()]

    return safety

def do_updr(s: Solver) -> None:
    if utils.args.use_z3_unsat_cores:
        z3.set_param('smt.core.minimize', True)

    if logic.check_init(s, safety_only=True, verbose=True) is not None:
        return

    if not utils.args.checkpoint_in:
        fs = updr.Frames(s)
    else:
        fs = updr.load_frames(utils.args.checkpoint_in, s)

    try:
        fs.search()
    except updr.AbstractCounterexample:
        pass

def debug_tokens(filename: str) -> None:
    l = parser.get_lexer()

    with open(filename) as f:
        l.input(f.read())

    while True:
        tok = l.token()
        if not tok:
            break      # No more input
        utils.logger.always_print(str(tok))

JSON = Dict[str, Any]
def json_counterexample(res: Union[Tuple[InvariantDecl, logic.Trace],
                                   Tuple[InvariantDecl, logic.Trace, syntax.DefinitionDecl]]) -> JSON:
    RT = Dict[syntax.RelationDecl, List[Tuple[List[str], bool]]]
    CT = Dict[syntax.ConstantDecl, str]
    FT = Dict[syntax.FunctionDecl, List[Tuple[List[str], str]]]

    inv = res[0]
    trace = res[1]
    if len(res) == 3:
        ition = res[2]  # type: ignore
    else:
        ition = None

    obj: JSON = {}
    obj['type'] = 'init' if ition is None else 'cti'

    if ition is not None:
        obj['transition'] = ition.name

    inv_json: JSON = {}
    if inv.name is not None:
        inv_json['name'] = inv.name
    if inv.span is not None:
        inv_json['line_number'] = inv.span[0].lineno
    inv_json['formula'] = str(inv.expr)
    obj['invariant'] = inv_json

    univs: List[JSON] = []
    for s, l in trace.univs.items():
        u: JSON = {}
        u['sort'] = s.name
        u['elements'] = l
        univs.append(u)
    obj['universes'] = univs

    def state_json(r: RT, c: CT, f: FT) -> JSON:
        obj: JSON = {}

        rels = []
        for rd, r_interp in r.items():
            r_obj: JSON = {}
            r_obj['name'] = rd.name
            tuples = []
            for t, b in r_interp:
                if b:
                    tuples.append(t)
            r_obj['interpretation'] = tuples
            rels.append(r_obj)
        obj['relations'] = rels

        consts = []
        for cd, c_interp in c.items():
            c_obj: JSON = {}
            c_obj['name'] = cd.name
            c_obj['interpretation'] = c_interp
            consts.append(c_obj)
        obj['constants'] = consts

        funcs = []
        for fd, f_interp in f.items():
            f_obj: JSON = {}
            f_obj['name'] = fd.name
            f_obj['interpretation'] = f_interp
            funcs.append(f_obj)
        obj['functions'] = funcs

        return obj

    obj['immutable'] = state_json(trace.immut_rel_interps,
                                  trace.immut_const_interps,
                                  trace.immut_func_interps)

    muts = []
    for i in range(len(trace.keys)):
        muts.append(state_json(trace.rel_interps[i],
                               trace.const_interps[i],
                               trace.func_interps[i]))
    obj['mutable'] = muts

    return obj

def json_verify_result(res: Union[Tuple[InvariantDecl, logic.Trace],
                                  Tuple[InvariantDecl, logic.Trace, syntax.DefinitionDecl]]) -> None:
    json_cex = json_counterexample(res)

    obj: JSON = {}
    obj['version'] = 1
    obj['subcommand'] = utils.args.subcommand
    obj['is_inductive'] = json_cex is None
    if json_cex is not None:
        obj['counterexample'] = json_cex
        json.dump(obj, sys.stdout, indent=4)

def verify(s: Solver) -> None:
    old_count = utils.error_count
    init_res = logic.check_init(s)
    tr_res = logic.check_transitions(s)
    res = init_res or tr_res
    if res is not None and utils.args.json:
        json_verify_result(res)

    if utils.error_count == old_count:
        utils.logger.always_print('all ok!')
    else:
        utils.logger.always_print('program has errors.')

def bmc(s: Solver) -> None:
    safety = syntax.And(*get_safety())

    n = utils.args.depth

    utils.logger.always_print('bmc checking the following property up to depth %d' % n)
    utils.logger.always_print('  ' + str(safety))

    if not utils.args.relax:
        bmcer = lambda bound: logic.check_bmc(s, safety, bound)
    else:
        bmcer = lambda bound: relaxed_traces.check_relaxed_bmc(safety, bound)

    for k in range(0, n + 1):
        if (m := bmcer(k)) is not None:
            if utils.args.print_counterexample:
                print('found violation')
                print(str(m))
            break
    else:
        print('no violation found.')

def theorem(s: Solver) -> None:
    utils.logger.always_print('checking theorems:')

    prog = syntax.the_program
    for th in prog.theorems():
        if th.num_states == 2:
            keys: Tuple[str, ...] = (KEY_OLD, KEY_NEW)
        elif th.num_states == 1:
            keys = (KEY_ONE,)
        else:
            keys = ()

        t = s.get_translator(keys)

        if th.name is not None:
            msg = ' ' + th.name
        elif th.span is not None:
            msg = ' on line %d' % th.span[0].lineno
        else:
            msg = ''

        utils.logger.always_print(' theorem%s... ' % msg, end='')
        sys.stdout.flush()

        with s.new_frame():
            s.add(z3.Not(t.translate_expr(th.expr)))

            logic.check_unsat([(th.span, 'theorem%s may not hold' % msg)], s, keys)

def nop(s: Solver) -> None:
    pass

def ipython(s: Solver) -> None:
    import IPython  # type: ignore
    # IPython.embed()
    IPython.start_ipython(argv=[], user_ns=dict(locals()))


def load_relaxed_trace_from_updr_cex(prog: Program, s: Solver) -> logic.Trace:
    import xml.dom.minidom  # type: ignore
    collection = xml.dom.minidom.parse("paxos_derived_trace.xml").documentElement

    components: List[syntax.TraceComponent] = []

    xml_decls = reversed(collection.childNodes)
    seen_first = False

    for elm in xml_decls:
        if isinstance(elm, xml.dom.minidom.Text):
            continue
        if elm.tagName == 'state':
            diagram = parser.parse_expr(elm.childNodes[0].data)
            diagram.resolve(prog.scope, syntax.BoolSort)
            assert isinstance(diagram, syntax.QuantifierExpr) and diagram.quant == 'EXISTS'
            active_clauses = [relaxed_traces.active_var(v.name, str(v.sort)) for v in diagram.vs()]

            if not seen_first:
                # restrict the domain to be subdomain of the diagram's existentials
                seen_first = True
                import itertools  # type: ignore
                for sort, vars in itertools.groupby(diagram.vs(), lambda v: v.sort):  # TODO; need to sort first
                    free_var = syntax.SortedVar(syntax.the_program.scope.fresh("v_%s" % str(sort)), None)

                    # TODO: diagram simplification omits them from the exists somewhere
                    consts = list(filter(lambda c: c.sort == sort, prog.constants()))
                    els: Sequence[Union[syntax.SortedVar, syntax.ConstantDecl]]
                    els = list(vars)
                    els += consts
                    restrict_domain = syntax.Forall([free_var],
                                                    syntax.Or(*(syntax.Eq(syntax.Id(free_var.name),
                                                                          syntax.Id(v.name))
                                                                for v in els)))
                    active_clauses += [restrict_domain]

            diagram_active = syntax.Exists(diagram.vs(),
                                           syntax.And(diagram.body, *active_clauses))
            diagram_active.resolve(prog.scope, syntax.BoolSort)

            components.append(syntax.AssertDecl(expr=diagram_active))
        elif elm.tagName == 'action':
            action_name = elm.childNodes[0].data.split()[0]
            tcall = syntax.TransitionCalls(calls=[syntax.TransitionCall(target=action_name, args=None)])
            components.append(syntax.TraceTransitionDecl(transition=tcall))
        else:
            assert False, "unknown xml tagName"

    trace_decl = syntax.TraceDecl(components=components, sat=True)
    migrated_trace = bmc_trace(prog, trace_decl, s, lambda s, ks: logic.check_solver(s, ks, minimize=True), log=False)

    assert migrated_trace is not None
    import pickle
    pickle.dump(migrated_trace, open("migrated_trace.p", "wb"))
    return migrated_trace


def sandbox(s: Solver) -> None:
    ####################################################################################
    # SANDBOX for playing with relaxed traces
    import pickle
    trns: logic.Trace = pickle.load(open("paxos_trace.p", "rb"))

    diff_conjunctions = relaxed_traces.derived_rels_candidates_from_trace(trns, [], 2, 3)

    print("num candidate relations:", len(diff_conjunctions))
    for diffing_conjunction in diff_conjunctions:
        # print("relation:")
        # for conj in diffing_conjunction:
        #     print("\t %s" % str(conj))
        print(diffing_conjunction[1])

    derrel_name = syntax.the_program.scope.fresh("nder")
    (free_vars, def_expr) = diff_conjunctions[0]
    def_axiom = syntax.Forall(free_vars,
                              syntax.Iff(syntax.Apply(derrel_name,
                                                      [syntax.Id(v.name) for v in free_vars]),
                                         # TODO: extract pattern
                                         def_expr))

    derrel = syntax.RelationDecl(name=derrel_name,
                                 arity=[syntax.safe_cast_sort(var.sort) for var in free_vars],
                                 mutable=True, derived=def_axiom, annotations=[])

    # TODO: this irreversibly adds the relation to the context, wrap
    derrel.resolve(syntax.the_program.scope)
    syntax.the_program.decls.append(derrel)  # TODO: hack! because RelationDecl.resolve only adds to prog.scope
    s.mutable_axioms.extend([def_axiom])  # TODO: hack! currently we register these axioms only on solver init

    print("Trying derived relation:", derrel)

    # the new decrease_domain action incorporates restrictions that derived relations remain the same on active tuples
    new_decrease_domain = relaxed_traces.relaxation_action_def(syntax.the_program, fresh=False)
    new_prog = relaxed_traces.replace_relaxation_action(syntax.the_program, new_decrease_domain)
    new_prog.resolve()
    print(new_prog)

    syntax.the_program = new_prog

    # TODO: recover this, making sure the candidate blocks the trace
    # trace_decl = next(syntax.the_program.traces())
    # trns2_o = bmc_trace(new_prog, trace_decl, s, lambda s, ks: logic.check_solver(s, ks, minimize=True))
    # assert trns2_o is None

    # migrated_trace = load_relaxed_trace_from_updr_cex(syntax.the_program, s)
    import pickle
    trns2_o = pickle.load(open("migrated_trace.p", "rb"))

    trns2 = cast(logic.Trace, trns2_o)
    print(trns2)
    print()
    assert not relaxed_traces.is_rel_blocking_relax(
        trns2,
        ([(v, str(syntax.safe_cast_sort(v.sort))) for v in free_vars], def_expr))

    # for candidate in diff_conjunctions:
    #     print("start checking")
    #     print()
    #     if str(candidate[1]) == ('exists v0:node. member(v0, v1) & left_round(v0, v2) '
    #                              '& !vote(v0, v2, v3) & active_node(v0)'):
    #         print(candidate)
    #         assert False
    #         resush = relaxed_traces.is_rel_blocking_relax_step(
    #             trns2, 11,
    #             ([(v, str(syntax.safe_cast_sort(v.sort))) for v in candidate[0]],
    #              candidate[1]))
    #         # res2 = trns2.as_state(0).eval(syntax.And(*[i.expr for i in syntax.the_program.inits()]))
    #
    #         # resush = trns2.as_state(7).eval(syntax.And(*[i.expr for i in syntax.the_program.inits()]))
    #         print(resush)
    #         assert False
    # assert False

    diff_conjunctions = list(
        filter(lambda candidate:
               relaxed_traces.is_rel_blocking_relax(
                   trns2,
                   ([(v, str(syntax.safe_cast_sort(v.sort))) for v in candidate[0]], candidate[1])),
               diff_conjunctions))
    print("num candidate relations:", len(diff_conjunctions))
    for diffing_conjunction in diff_conjunctions:
        # print("relation:")
        # for conj in diffing_conjunction:
        #     print("\t %s" % str(conj))
        print(diffing_conjunction[1])

    print()

    assert False

    ####################################################################################

def trace(s: Solver) -> None:
    # sandbox(s)

    prog = syntax.the_program
    traces = list(prog.traces())
    if traces:
        utils.logger.always_print('finding traces:')

    for trace in traces:
        res = bmc_trace(prog, trace, s, lambda s, keys: logic.check_unsat([], s, keys), log=True)
        if (res is not None) != trace.sat:
            def bool_to_sat(b: bool) -> str:
                return 'sat' if b else 'unsat'
            utils.print_error(trace.span, 'trace declared %s but was %s!' %
                              (bool_to_sat(trace.sat), bool_to_sat(res is not None)))


def check_one_bounded_width_invariant(s: Solver) -> None:
    prog = syntax.the_program
    other_decls = [d for d in prog.decls if not isinstance(d, InvariantDecl)]
    invs = list(prog.invs())
    R: Set[InvariantDecl] = set()

    def check() -> bool:
        prog.decls = other_decls + list(R)
        if logic.check_init(s, minimize=False, verbose=False) is not None:
            return False
        if logic.check_transitions(s, minimize=False, verbose=False) is not None:
            return False

        return True

    while len(R) != len(invs):
        did_something = False
        for inv in invs:
            if inv in R:
                continue
            print('trying to add', inv, '...', end='')
            R.add(inv)
            if check():
                print('added')
                did_something = True
            else:
                print('failed to add')
                R.remove(inv)
        if not did_something:
            break
    result = len(R) == len(invs)
    if result:
        print('invariant is 1-provable')
    else:
        print('invariant is not 1-provable, but here is the maximal subset that is')
        for inv in R:
            print(inv)


def relax(s: Solver) -> None:
    print(relaxed_traces.relaxed_program(syntax.the_program))

def parse_args(args: List[str]) -> utils.MypyvyArgs:
    argparser = argparse.ArgumentParser()

    subparsers = argparser.add_subparsers(title='subcommands', dest='subcommand')
    all_subparsers = []

    verify_subparser = subparsers.add_parser('verify', help='verify that the invariants are inductive')
    verify_subparser.set_defaults(main=verify)
    all_subparsers.append(verify_subparser)

    updr_subparser = subparsers.add_parser(
        'updr',
        help='search for a strengthening that proves the invariant named by the --safety=NAME flag')
    updr_subparser.set_defaults(main=do_updr)
    all_subparsers.append(updr_subparser)

    bmc_subparser = subparsers.add_parser(
        'bmc',
        help='bounded model check to depth given by the --depth=DEPTH flag '
             'for property given by the --safety=NAME flag')
    bmc_subparser.set_defaults(main=bmc)
    all_subparsers.append(bmc_subparser)

    theorem_subparser = subparsers.add_parser(
        'theorem',
        help='check state-independent theorems about the background axioms of a model')
    theorem_subparser.set_defaults(main=theorem)
    all_subparsers.append(theorem_subparser)

    trace_subparser = subparsers.add_parser(
        'trace',
        help='search for concrete executions that satisfy query described by the file\'s trace declaration')
    trace_subparser.set_defaults(main=trace)
    all_subparsers.append(trace_subparser)

    generate_parser_subparser = subparsers.add_parser(
        'generate-parser',
        help='internal command used by benchmarking infrastructure to avoid certain race conditions')
    # parser is generated implicitly by main when it parses the program, so we can just nop here
    generate_parser_subparser.set_defaults(main=nop)
    all_subparsers.append(generate_parser_subparser)

    typecheck_subparser = subparsers.add_parser('typecheck', help='typecheck the file, report any errors, and exit')
    typecheck_subparser.set_defaults(main=nop)  # program is always typechecked; no further action required
    all_subparsers.append(typecheck_subparser)

    relax_subparser = subparsers.add_parser(
        'relax',
        help='produce a version of the file that is "relaxed", '
             'in a way that is indistinguishable for universal invariants')
    relax_subparser.set_defaults(main=relax)
    all_subparsers.append(relax_subparser)

    check_one_bounded_width_invariant_parser = subparsers.add_parser(
        'check-one-bounded-width-invariant',
        help='popl'
    )
    check_one_bounded_width_invariant_parser.set_defaults(main=check_one_bounded_width_invariant)
    all_subparsers.append(check_one_bounded_width_invariant_parser)

    all_subparsers += pd.add_argparsers(subparsers)

    all_subparsers += rethink.add_argparsers(subparsers)

    all_subparsers += sep.add_argparsers(subparsers)

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
        s.add_argument('--print-program',
                       choices=['str', 'repr', 'faithful', 'refactor-old-to-new', 'without-invariants'],
                       help='print program after parsing using given strategy')
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
        s.add_argument('--print-negative-tuples', action=utils.YesNoAction, default=False,
                       help='print negative counterexamples')
        s.add_argument('--print-cmdline', action=utils.YesNoAction, default=True,
                       help='print the command line passed to mypyvy')
        s.add_argument('--clear-cache', action=utils.YesNoAction, default=False,
                       help='do not load from cache, but dump to cache as usual '
                            '(effectively clearing the cache before starting)')
        s.add_argument('--clear-cache-memo', action=utils.YesNoAction, default=False,
                       help='load only discovered states from the cache, but dump to cache as usual '
                            '(effectively clearing the memoization cache before starting, '
                            'while keeping discovered states and transitions)')
        s.add_argument('--cache-only', action=utils.YesNoAction, default=False,
                       help='assert that the caches already contain all the answers')
        s.add_argument('--cache-only-discovered', action=utils.YesNoAction, default=False,
                       help='assert that the discovered states already contain all the answers')
        s.add_argument('--print-exit-code', action=utils.YesNoAction, default=False,
                       help='print the exit code before exiting (good for regression testing)')
        s.add_argument('--accept-old', action=utils.YesNoAction, default=False,
                       help='allow deprecated syntax using old()')

        s.add_argument('--cvc4', action='store_true',
                       help='use CVC4 as the backend solver. this is not very well supported.')

        s.add_argument('--smoke-test-solver', action=utils.YesNoAction, default=False,
                       help='(for debugging mypyvy itself) double check countermodels by evaluation')


        # for diagrams:
        s.add_argument('--simplify-diagram', action=utils.YesNoAction,
                       default=(s is updr_subparser),
                       default_description='yes for updr, else no',
                       help='in diagram generation, substitute existentially quantified variables '
                            'that are equal to constants')

    updr_subparser.add_argument('--use-z3-unsat-cores', action=utils.YesNoAction, default=True,
                                help='generalize using unsat cores rather than brute force')
    updr_subparser.add_argument('--assert-inductive-trace', action=utils.YesNoAction, default=False,
                                help='(for debugging mypyvy itself) check that frames are always inductive')

    verify_subparser.add_argument('--check-transition', default=None, nargs='+',
                                  help="when verifying inductiveness, check only these transitions")
    verify_subparser.add_argument('--check-invariant', default=None, nargs='+',
                                  help="when verifying inductiveness, check only these invariants")
    verify_subparser.add_argument('--json', action='store_true',
                                  help="output machine-parseable verification results in JSON format")

    updr_subparser.add_argument('--checkpoint-in',
                                help='start from internal state as stored in given file')
    updr_subparser.add_argument('--checkpoint-out',
                                help='store internal state to given file')  # TODO: say when

    bmc_subparser.add_argument('--safety', help='property to check')
    bmc_subparser.add_argument('--depth', type=int, default=3, metavar='N',
                               help='number of steps to check')
    bmc_subparser.add_argument('--relax', action=utils.YesNoAction, default=False,
                               help='relaxed semantics (domain can decrease)')

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

    def formatTime(self, record: Any, datefmt: Optional[str] = None) -> str:
        return str((datetime.now() - self.start).total_seconds())

def parse_program(input: str, forbid_rebuild: bool = False, filename: Optional[str] = None) -> Program:
    l = parser.get_lexer()
    p = parser.get_parser(forbid_rebuild=forbid_rebuild)
    prog: Program = p.parse(input=input, lexer=l, filename=filename)
    prog.input = input
    return prog

def main() -> None:
    # limit RAM usage to 45 GB
    # TODO: make this a command line argument
    # TODO: not sure if this is actually the right way to do this (also, what about child processes?)
    resource.setrlimit(resource.RLIMIT_AS, (90 * 10**9, 90 * 10**9))

    utils.args = parse_args(sys.argv[1:])

    if utils.args.log_xml:
        fmt = '%(message)s'
    elif utils.args.log_time:
        fmt = '%(asctime)s %(filename)s:%(lineno)d: %(message)s'
    else:
        fmt = '%(filename)s:%(lineno)d: %(message)s'

    if 'json' in utils.args and utils.args.json:
        utils.args.log = 'critical'

    utils.logger.setLevel(getattr(logging, utils.args.log.upper(), None))
    handler = logging.StreamHandler(stream=sys.stdout)
    handler.terminator = ''
    handler.setFormatter(MyFormatter(fmt))
    logging.root.addHandler(handler)

    if utils.args.print_cmdline:
        utils.logger.always_print(' '.join([sys.executable] + sys.argv))
        utils.logger.info('Running mypyvy with the following options:')
        for k, v in sorted(vars(utils.args).items()):
            utils.logger.info(f'    {k} = {v!r}')

    utils.logger.info('setting seed to %d' % utils.args.seed)
    z3.set_param('smt.random_seed', utils.args.seed)
    z3.set_param('sat.random_seed', utils.args.seed)

    # utils.logger.info('enable z3 macro finder')
    # z3.set_param('smt.macro_finder', True)

    if utils.args.timeout is not None:
        utils.logger.info('setting z3 timeout to %s' % utils.args.timeout)
        z3.set_param('timeout', utils.args.timeout)

    pre_parse_error_count = utils.error_count

    with open(utils.args.filename) as f:
        prog = parse_program(f.read(), forbid_rebuild=utils.args.forbid_parser_rebuild,
                             filename=utils.args.filename)

    if utils.error_count > pre_parse_error_count:
        utils.logger.always_print('program has syntax errors.')
        utils.exit(1)

    if utils.args.print_program is not None:
        if utils.args.print_program == 'str':
            to_str: Callable[[Program], str] = str
            end = '\n'
        elif utils.args.print_program == 'repr':
            to_str = repr
            end = '\n'
        elif utils.args.print_program == 'faithful':
            to_str = syntax.faithful_print_prog
            end = ''
        elif utils.args.print_program == 'without-invariants':
            def p(prog: Program) -> str:
                return syntax.faithful_print_prog(prog, skip_invariants=True)
            to_str = p
            end = ''
        elif utils.args.print_program == 'refactor-old-to-new':
            pre_vocab_resolution_error_count = utils.error_count
            prog.resolve_vocab()
            if utils.error_count > pre_vocab_resolution_error_count:
                print('program has resolution errors')
                utils.exit(1)
            pre_translation_error_count = utils.error_count
            new_prog = syntax.translate_old_to_new_prog(prog, strip_old=False)
            if utils.error_count > pre_translation_error_count:
                print('errors during old->new translation')
                utils.exit(1)
            print(syntax.faithful_print_prog(new_prog, ignore_old=True), end='')
            utils.exit(0)
        else:
            assert False

        utils.logger.always_print(to_str(prog), end=end)

    pre_resolve_error_count = utils.error_count

    prog.resolve()
    if utils.error_count > pre_resolve_error_count:
        utils.logger.always_print('program has resolution errors.')
        utils.exit(1)

    syntax.the_program = prog

    s = Solver(use_cvc4=utils.args.cvc4)

    # initialize common keys
    s.get_translator((KEY_ONE,))
    s.get_translator((KEY_NEW,))
    s.get_translator((KEY_OLD,))

    utils.args.main(s)

    if utils.args.ipython:
        ipython(s)

    utils.exit(1 if utils.error_count > 0 else 0)


if __name__ == '__main__':
    main()
