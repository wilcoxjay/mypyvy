#!/usr/bin/env python3.7

from __future__ import annotations
import argparse
from datetime import datetime
import logging
import sys
from typing import Any, cast, Dict, List, Optional, TypeVar
import z3
import resource

import logic
from logic import Solver, KEY_NEW, KEY_OLD, KEY_ONE
import parser
import syntax
from syntax import Expr, Program, InvariantDecl, AutomatonDecl
import updr
import utils
import itertools

import pd

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
            e = syntax.close_free_vars(None, parser.parse_expr(utils.args.safety))
            e.resolve(prog.scope, syntax.BoolSort)
            safety = [e]
    else:
        safety = [s.expr for s in prog.safeties()]

    return safety


@utils.log_start_end_xml(utils.logger, logging.INFO)
@utils.log_start_end_time(utils.logger, logging.INFO)
def do_updr(s: Solver) -> None:
    if utils.args.use_z3_unsat_cores:
        z3.set_param('smt.core.minimize', True)

    logic.check_init(s, safety_only=True)

    fs = updr.Frames(s)
    try:
        fs.search()
    except updr.AbstractCounterexample:
        pass
    finally:
        utils.logger.info(f'updr learned {fs.state_count} states (possibly with duplicates)')

        utils.logger.info(f'updr learned {len(fs.predicates)} predicates (no duplicates)')
        # for x in fs.predicates:
        #     utils.logger.info(str(x))

def debug_tokens(filename: str) -> None:
    l = parser.get_lexer()

    with open(filename) as f:
        l.input(f.read())

    while True:
        tok = l.token()
        if not tok:
            break      # No more input
        utils.logger.always_print(str(tok))


def check_automaton_init(s: Solver, a: AutomatonDecl) -> None:
    utils.logger.always_print('checking automaton init:')

    prog = syntax.the_program

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

                logic.check_unsat([(inv.tok, 'phase invariant%s may not hold in initial state' % msg)], s, [KEY_ONE])

def check_automaton_edge_covering(s: Solver, a: AutomatonDecl) -> None:
    utils.logger.always_print('checking automaton edge covering:')

    prog = syntax.the_program

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
                                      s, [KEY_OLD, KEY_NEW])


def check_automaton_inductiveness(s: Solver, a: AutomatonDecl) -> None:
    utils.logger.always_print('checking automaton inductiveness:')

    prog = syntax.the_program
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
                                              s, [KEY_OLD, KEY_NEW])

@utils.log_start_end_time(utils.logger, logging.INFO)
def verify(s: Solver) -> None:
    old_count = utils.error_count
    prog = syntax.the_program
    a = prog.the_automaton()
    if a is None:
        if utils.args.automaton == 'only':
            utils.print_error_and_exit(None, "--automaton='only' requires the file to declare an automaton")
    elif utils.args.automaton != 'no':
        check_automaton_full(s, a)

    if utils.args.automaton != 'only':
        logic.check_init(s)
        logic.check_transitions(s)

    if utils.error_count == old_count:
        utils.logger.always_print('all ok!')
    else:
        utils.logger.always_print('program has errors.')

def check_automaton_full(s: Solver, a: AutomatonDecl) -> None:
    check_automaton_init(s, a)
    check_automaton_inductiveness(s, a)
    check_automaton_edge_covering(s, a)

@utils.log_start_end_time(utils.logger)
def bmc(s: Solver) -> None:
    safety = syntax.And(*get_safety())

    n = utils.args.depth

    utils.logger.always_print('bmc checking the following property up to depth %d' % n)
    utils.logger.always_print('  ' + str(safety))

    for k in range(0, n + 1):
        m = logic.check_bmc(s, safety, k)
        if m is not None:
            if utils.args.print_counterexample:
                print('found violation')
                print(str(m))
            break
    else:
        print('no violation found.')


@utils.log_start_end_time(utils.logger)
def theorem(s: Solver) -> None:
    utils.logger.always_print('checking theorems:')

    prog = syntax.the_program
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

            logic.check_unsat([(th.tok, 'theorem%s may not hold' % msg)], s, keys)

def nop(s: Solver) -> None:
    pass

def ipython(s: Solver) -> None:
    import IPython  # type: ignore
    # IPython.embed()
    IPython.start_ipython(argv=[], user_ns=dict(locals()))

def translate_transition_call(s: Solver, key: str, key_old: str, c: syntax.TransitionCall) -> z3.ExprRef:
    prog = syntax.the_program
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
    qs1 = [q for q in qs if q is not None]
    with lator.scope.in_scope(ition.binder, bs):
        body = lator.translate_transition_body(ition)
    if len(qs1) > 0:
        return z3.Exists(qs1, body)
    else:
        return body

def dict_val_from_rel_name(name: str, m: Dict[syntax.RelationDecl,T]) -> T:
    for r,v in m.items():
        if r.name != name:
            continue
        return v
    raise KeyError

def trace(s: Solver) -> None:
    ####################################################################################
    # SANDBOX for playing with relaxed traces
    import pickle
    trns: logic.Trace = pickle.load(open("paxos_trace.p", "rb"))
    first_relax_idx = trns.transitions.index('decrease_domain')
    assert first_relax_idx != -1, trns.transitions
    assert first_relax_idx + 1 < len(trns.keys)
    pre_relax_state = trns.as_state(first_relax_idx)
    post_relax_state = trns.as_state(first_relax_idx + 1)
    assert pre_relax_state.univs == post_relax_state.univs


    # relaxed elements
    relaxed_elements = []
    for sort, univ in pre_relax_state.univs.items():
        active_rel_name = 'active_' + sort.name         # TODO: de-duplicate
        pre_active_interp = dict_val_from_rel_name(active_rel_name, pre_relax_state.rel_interp)
        post_active_interp = dict_val_from_rel_name(active_rel_name, post_relax_state.rel_interp)
        pre_active_elements = [tup[0] for (tup, b) in pre_active_interp if b]
        post_active_elements = [tup[0] for (tup, b) in post_active_interp if b]
        assert set(post_active_elements).issubset(set(pre_active_elements))

        for relaxed_elem in utils.OrderedSet(pre_active_elements) - set(post_active_elements):
            relaxed_elements.append((sort, relaxed_elem))

    # pre-relaxation step facts concerning at least one relaxed element (other to be found by UPDR)
    relevant_facts = []
    # TODO: also functions + constants + inequalities
    for rel, intp in pre_relax_state.rel_interp.items():
        for fact in intp:
            (elms, _) = fact
            if set(elms) & set(ename for (_, ename) in relaxed_elements):
                relevant_facts.append((rel, fact))

    # facts blocking this specific relaxation step
    NUM_FACTS_IN_DERIVED_REL = 1
    diff_conjunctions = []
    candidates_cache = set()
    for fact_lst in itertools.combinations(relevant_facts, NUM_FACTS_IN_DERIVED_REL):
        elements = utils.OrderedSet(itertools.chain.from_iterable(elms for (_, (elms, _)) in fact_lst))
        vars_from_elm = dict((elm, syntax.SortedVar(None, syntax.the_program.scope.fresh("v%d" % i), None))
                                for (i, elm) in enumerate(elements))
        parameter_elements = elements - set(elm for (_, elm) in relaxed_elements)

        conjuncts = []
        for rel, fact in fact_lst:
            (fact_els, fact_true) = fact
            fact_free_vars = syntax.Apply(rel.name, [syntax.Id(None, vars_from_elm[e].name) for e in fact_els])
            if not fact_true:
                fact_free_vars = syntax.Not(fact_free_vars)
            conjuncts.append(fact_free_vars)

        for elm, var in vars_from_elm.items():
            sort = pre_relax_state.element_sort(elm)
            active_element_conj = syntax.Apply('active_%s' % sort.name, [syntax.Id(None, var.name)])
            conjuncts.append(active_element_conj)

        derived_relation_formula = syntax.Exists([vars_from_elm[elm]
                                                  for (_, elm) in relaxed_elements
                                                  if elm in elements],
                                                 syntax.And(*conjuncts))

        diffing_formula = syntax.Exists([vars_from_elm[elm] for elm in parameter_elements],
                                        syntax.And(syntax.Old(derived_relation_formula),
                                                   syntax.Not(derived_relation_formula)))
        with syntax.the_program.scope.two_state(twostate=True): # TODO: what is this doing? probably misusing
            diffing_formula.resolve(syntax.the_program.scope, syntax.BoolSort)

        if str(diffing_formula) in candidates_cache:
            continue
        candidates_cache.add(str(diffing_formula))

        if trns.eval_double_vocab(diffing_formula, first_relax_idx):
            diff_conjunctions.append(derived_relation_formula)

    print("num candidate relations:", len(diff_conjunctions))
    for diffing_conjunction in diff_conjunctions:
        # print("relation:")
        # for conj in diffing_conjunction:
        #     print("\t %s" % str(conj))
        print(diffing_conjunction)

    assert False

    ####################################################################################

    prog = syntax.the_program
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
                        logic.assert_any_transition(s, str(i), keys[i + 1], keys[i], allow_stutter=True)
                    else:
                        l = []
                        for call in te.calls:
                            tid = z3.Bool(logic.get_transition_indicator(str(i), call.target))
                            l.append(tid)
                            s.add(tid == translate_transition_call(s, keys[i + 1], keys[i], call))
                        s.add(z3.Or(*l))

                    i += 1

            res = logic.check_unsat([], s, keys)
            if (res is not None) != trace.sat:
                utils.print_error(trace.tok, 'trace declared %s but was %s!' % ('sat' if trace.sat else 'unsat', res))

def relax(s: Solver) -> None:
    prog = syntax.the_program

    new_decls: List[syntax.Decl] = [d for d in prog.sorts()]

    actives: Dict[syntax.SortDecl, syntax.RelationDecl] = {}
    for sort in prog.sorts():
        name = prog.scope.fresh('active_' + sort.name)
        r = syntax.RelationDecl(None, name, arity=[syntax.UninterpretedSort(None, sort.name)],
                                mutable=True, derived=None, annotations=[])
        actives[sort] = r
        new_decls.append(r)

    # active relations initial conditions: always true
    for sort in prog.sorts():
        name = prog.scope.fresh(sort.name[0].upper())
        expr = syntax.Forall([syntax.SortedVar(None, name, None)],
                             syntax.Apply(actives[sort].name, [syntax.Id(None, name)]))
        new_decls.append(syntax.InitDecl(None, name=None, expr=expr))

    for d in prog.decls:
        if isinstance(d, syntax.SortDecl):
            pass  # already included above
        elif isinstance(d, syntax.RelationDecl):
            if d.derived_axiom is not None:
                expr = syntax.relativize_quantifiers(actives, d.derived_axiom)
                new_decls.append(syntax.RelationDecl(None, d.name, d.arity, d.mutable, expr,
                                                     d.annotations))
            else:
                new_decls.append(d)
        elif isinstance(d, syntax.ConstantDecl):
            new_decls.append(d)
        elif isinstance(d, syntax.FunctionDecl):
            new_decls.append(d)
        elif isinstance(d, syntax.AxiomDecl):
            new_decls.append(d)
        elif isinstance(d, syntax.InitDecl):
            new_decls.append(d)
        elif isinstance(d, syntax.DefinitionDecl):
            assert not isinstance(d.body, syntax.BlockStatement), \
                "relax does not support transitions written in imperative syntax"
            mods, expr = d.body
            expr = syntax.relativize_quantifiers(actives, expr, old=d.twostate)
            if d.public:
                guard = syntax.relativization_guard_for_binder(actives, d.binder, old=True)
                expr = syntax.And(guard, expr)
            new_decls.append(syntax.DefinitionDecl(None, d.public, d.twostate, d.name,
                                                   params=d.binder.vs, body=(mods, expr)))
        elif isinstance(d, syntax.InvariantDecl):
            expr = syntax.relativize_quantifiers(actives, d.expr)
            new_decls.append(syntax.InvariantDecl(None, d.name, expr=expr,
                                                  is_safety=d.is_safety, is_sketch=d.is_sketch))
        else:
            assert False, d

    decrease_name = prog.scope.fresh('decrease_domain')
    mods = []
    conjs: List[Expr] = []

    # a conjunct allowing each domain to decrease
    for sort in prog.sorts():
        name = prog.scope.fresh(sort.name[0].upper())
        ap = syntax.Apply(actives[sort].name, [syntax.Id(None, name)])
        expr = syntax.Forall([syntax.SortedVar(None, name, None)],
                             syntax.Implies(ap, syntax.Old(ap)))
        conjs.append(expr)
        mods.append(syntax.ModifiesClause(None, actives[sort].name))

    # constants are active
    for const in prog.constants():
        conjs.append(syntax.Apply(actives[syntax.get_decl_from_sort(const.sort)].name,
                                  [syntax.Id(None, const.name)]))

    # functions map active to active
    for func in prog.functions():
        names: List[str] = []
        func_conjs = []
        for arg_sort in func.arity:
            arg_sort_decl = syntax.get_decl_from_sort(arg_sort)
            name = prog.scope.fresh(arg_sort_decl.name[0].upper(),
                                    also_avoid=names)
            names.append(name)
            func_conjs.append(syntax.Apply(actives[arg_sort_decl].name, [syntax.Id(None, name)]))
        ap_func = syntax.Old(syntax.Apply(func.name, [syntax.Id(None, name) for name in names]))
        active_func = syntax.Apply(actives[syntax.get_decl_from_sort(func.sort)].name, [ap_func])
        conjs.append(syntax.Forall([syntax.SortedVar(None, name, None) for name in names],
                                   syntax.Implies(syntax.And(*func_conjs), active_func)))

    # (relativized) axioms hold after relaxation
    for axiom in prog.axioms():
        if not syntax.is_universal(axiom.expr):
            conjs.append(syntax.relativize_quantifiers(actives, axiom.expr))

    # derived relations have the same interpretation on the active domain
    for rel in prog.derived_relations():
        names = []
        rel_conjs = []
        for arg_sort in rel.arity:
            arg_sort_decl = syntax.get_decl_from_sort(arg_sort)
            name = prog.scope.fresh(arg_sort_decl.name[0].upper(),
                                    also_avoid=names)
            names.append(name)
            rel_conjs.append(syntax.Apply(actives[arg_sort_decl].name, [syntax.Id(None, name)]))
        ap_rel = syntax.Apply(rel.name, [syntax.Id(None, name) for name in names])
        conjs.append(syntax.Forall([syntax.SortedVar(None, name, None) for name in names],
                                   syntax.Implies(syntax.And(*rel_conjs),
                                                  syntax.Iff(ap_rel, syntax.Old(ap_rel)))))

    new_decls.append(syntax.DefinitionDecl(None, public=True, twostate=True, name=decrease_name,
                                           params=[], body=(mods, syntax.And(*conjs))))
    print(Program(new_decls))

def parse_args(args: List[str]) -> utils.MypyvyArgs:
    argparser = argparse.ArgumentParser()

    subparsers = argparser.add_subparsers(title='subcommands', dest='subcommand')
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

    relax_subparser = subparsers.add_parser('relax', help='produce a version of the file that is "relaxed", in a way that is indistinguishable for universal invariants')
    relax_subparser.set_defaults(main=relax)
    all_subparsers.append(relax_subparser)

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
        s.add_argument('--clear-cache', action=utils.YesNoAction, default=False,
                       help='do not load from cache, but dump to cache as usual (effectively clearing the cache before starting)')
        s.add_argument('--clear-cache-memo', action=utils.YesNoAction, default=False,
                       help='load only discovered states from the cache, but dump to cache as usual (effectively clearing the memoization cache before starting, while keeping discovered states and transitions)')
        s.add_argument('--cache-only', action=utils.YesNoAction, default=False,
                       help='assert that the caches already contain all the answers')
        s.add_argument('--cache-only-discovered', action=utils.YesNoAction, default=False,
                       help='assert that the discovered states already contain all the answers')

        # for diagrams:
        s.add_argument('--simplify-diagram', action=utils.YesNoAction,
                       default=(s is updr_subparser),
                       default_description='yes for updr, else no',
                       help='in diagram generation, substitute existentially quantified variables that are equal to constants')
        s.add_argument('--diagrams-subclause-complete', action=utils.YesNoAction, default=False,
                       help='in diagram generation, "complete" the diagram so that every stronger '
                            'clause is a subclause')

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

    def formatTime(self, record: Any, datefmt: Optional[str] = None) -> str:
        return str((datetime.now() - self.start).total_seconds())

def parse_program(input: str, force_rebuild: bool = False, filename: Optional[str] = None) -> Program:
    l = parser.get_lexer()
    p = parser.get_parser(forbid_rebuild=force_rebuild)
    return p.parse(input=input, lexer=l, filename=filename)

def main() -> None:
    resource.setrlimit(resource.RLIMIT_AS, (90*10**9, 90*10**9))  # limit RAM usage to 45 GB # TODO: make this a command line argument # TODO: not sure if this is actually the right way to do this (also, what about child processes?)

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

    with utils.LogTag(utils.logger, 'main', lvl=logging.INFO):
        if utils.args.print_cmdline:
            with utils.LogTag(utils.logger, 'options', lvl=logging.INFO):
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

        syntax.the_program = prog

        s = Solver()

        # initialize common keys
        s.get_translator(KEY_ONE)
        s.get_translator(KEY_NEW)
        s.get_translator(KEY_OLD)

        utils.args.main(s)

        utils.logger.info('total number of queries: %s' % s.nqueries)

        if utils.args.ipython:
            ipython(s)

    sys.exit(1 if utils.error_count > 0 else 0)


if __name__ == '__main__':
    main()
