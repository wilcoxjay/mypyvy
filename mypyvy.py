import z3
import sys
from typing import List, Any, Optional, Callable, Set, Tuple, Union, Iterable, Dict, TypeVar, Sequence
import copy
import datetime
import logging
import argparse

z3.Forall = z3.ForAll # type: ignore

def solver_enter(self): # type: ignore
    self.push()

def solver_exit(self, exn_type, exn_value, traceback): # type: ignore
    self.pop()

z3.Solver.__enter__ = solver_enter # type: ignore
z3.Solver.__exit__ = solver_exit # type: ignore

import parser, syntax

T = TypeVar('T')

def _product(l, x, i): # type: (Sequence[Sequence[T]], List[T], int) -> Iterable[List[T]]
    assert len(l) == len(x)

    if i >= len(l):
        yield x
    else:
        for y in l[i]:
            x[i] = y
            for z in _product(l, x, i+1):
                yield z

def product(l): # type: (Sequence[Sequence[T]]) -> Iterable[List[T]]
    if l == []:
        yield []
    else:
        if l[0] == []:
            pass
        else:
            x = [l[0][0] for i in range(len(l))]
            for z in _product(l, x, 0):
                yield z

#         print ''
#         print 'sorts:'
#         for sort in m.sorts():
#             print ' ', sort, ': ', m.get_universe(sort)
# 
#         print ''
#         print 'old decls:'
#         for decl in m.decls():
#             if str(decl).startswith('old'):
#                 print ' ', decl, ': '
#                 domains = []
#                 for i in range(decl.arity()):
#                     domains.append(m.get_universe(decl.domain(i)))
# 
#                 for x in product(domains):
#                     print '%s(%s) = %s' % (decl, ', '.join(str(y) for y in x), m.eval(decl(x)))

def check_unsat(s, prog, key, key_old=None): # type: (z3.Solver, syntax.Program, str, Optional[str]) -> None
    # print s.to_smt2()

    res = s.check()

    if res != z3.unsat:
        m = Model(prog, s.model(), key, key_old)

        print('')
        print(m)
        raise Exception('no')
    print('ok.')

def check_init(s, prog): # type: (z3.Solver, syntax.Program) -> None
    print('checking init:')

    with s:
        for init in prog.inits():
            s.add(init.expr.to_z3('one'))

        for inv in prog.invs():
            with s:
                s.add(z3.Not(inv.expr.to_z3('one')))

                print('  implies invariant %s...' % \
                    (inv.name if inv.name is not None else 'on line %s' % inv.tok.lineno \
                     if inv.tok is not None else '',), end=' ')

                check_unsat(s, prog, 'one')


def check_transitions(s, prog): # type: (z3.Solver, syntax.Program) -> None
    with s:
        for inv in prog.invs():
            s.add(inv.expr.to_z3('old'))

        for t in prog.transitions():
            print('checking transation %s:' % (t.name,))

            with s:
                s.add(t.to_z3('new', 'old'))
                for inv in prog.invs():
                    with s:
                        s.add(z3.Not(inv.expr.to_z3('new')))

                        print('  preserves invariant %s...' % \
                            (inv.name if inv.name is not None else 'on line %s' % inv.tok.lineno \
                             if inv.tok is not None else '',), end=' ')
                        sys.stdout.flush()

                        check_unsat(s, prog, 'new', 'old')

def check_implication(s, hyps, concs):
    # type: (z3.Solver, Iterable[syntax.Expr], Iterable[syntax.Expr]) -> Optional[z3.ModelRef]
    with s:
        for e in hyps:
            s.add(e.to_z3('one'))
        for e in concs:
            with s:
                s.add(z3.Not(e.to_z3('one')))
                res = s.check()

                if res != z3.unsat:
                    return s.model()

    return None

def check_two_state_implication_all_transitions(s, prog, old_hyps, new_conc):
    # type: (z3.Solver, syntax.Program, Iterable[syntax.Expr], syntax.Expr) -> Optional[z3.ModelRef]
    with s:
        for h in old_hyps:
            s.add(h.to_z3('old'))

        s.add(z3.Not(new_conc.to_z3('new')))

        for t in prog.transitions():
            with s:
                s.add(t.to_z3('new', 'old'))

                if s.check() != z3.unsat:
                    return s.model()

    return None


def safe_resolve(e, scope, sort): # type: (syntax.Expr, syntax.Scope, syntax.InferenceSort) -> None
    try:
        e.resolve(scope, sort)
    except Exception as exn:
        print('internal error: tried to construct unresolvable intermediate expression')
        print(e)
        print(exn)
        raise exn

class Diagram(object):
    # This class represents a formula of the form
    #
    #     exists X1, ..., X_k.
    #         C1 & C2 & ... & C_n
    #
    # in a way that is slightly more convenient than a usual ast for computing an
    # unsat core of the C_i.  Instead of just an ast, this class stores a list of
    # vars and a list of conjuncts.  In order to make resolution work seamlessly,
    # it also constructs an internal ast of the formula, which structurally shares
    # all the conjuncts from the list.  This ast is ignored except for purposes
    # of resolving all the C_i.

    def __init__(self, vs, conjuncts): # type: (List[syntax.SortedVar], List[syntax.Expr]) -> None
        self.vs = vs
        self.conjuncts = conjuncts
        self.q = syntax.QuantifierExpr(None, 'EXISTS', vs, syntax.And(*self.conjuncts))
        self.trackers = [] # type: List[z3.ExprRef]

    def __str__(self): # type: () -> str
        return 'exists %s.\n  %s' % (
            ', '.join(v.name for v in self.vs),
            ' &\n  '.join(str(c) for c in self.conjuncts)
        )

    def resolve(self, scope): # type: (syntax.Scope) -> None
        safe_resolve(self.q, scope, syntax.BoolSort)

    def to_z3(self, key): # type: (str) -> z3.ExprRef
        bs = []
        for sv in self.vs:
            n = sv.name
            assert sv.sort is not None and not isinstance(sv.sort, syntax.SortInferencePlaceholder)
            self.q.binders[n] = z3.Const(n, sv.sort.to_z3())
            bs.append(self.q.binders[n])

        z3conjs = []
        self.trackers = []
        for i, c in enumerate(self.conjuncts):
            p = z3.Bool('p%d' % i)
            self.trackers.append(p)
            z3conjs.append(p == c.to_z3(key))

        if len(bs) > 0:
            return z3.Exists(bs, z3.And(*z3conjs))
        else:
            return z3.And(*z3conjs)

    def to_ast(self): # type: () -> syntax.Expr
        if len(self.conjuncts) == 0:
            return syntax.Bool(None, True)
        elif len(self.vs) == 0:
            return self.q.body
        else:
            return self.q

    def _reinit(self): # type: () -> None
        self.q.vs = self.vs
        self.q.body = syntax.And(*self.conjuncts)
        self.q.binders = {}

    def minimize_from_core(self, core): # type: (Set[int]) -> None
        assert len(core) > 0

        self.conjuncts = [self.conjuncts[i] for i in core]
        self.prune_unused_vars()

    def remove_clause(self, i): # type: (int) -> syntax.Expr
        c = self.conjuncts.pop(i)
        self._reinit()
        return c

    def add_clause(self, i, c): # type: (int, syntax.Expr) -> None
        self.conjuncts.insert(i, c)
        self._reinit()

    def prune_unused_vars(self): # type: () -> None
        self.vs = [v for v in self.vs if any(v.name in c.free_ids() for c in self.conjuncts)]
        self._reinit()

class Model(object):
    def __init__(self, prog, m, key, key_old=None):
        # type: (syntax.Program, z3.ModelRef, str, Optional[str]) -> None
        self.prog = prog
        self.z3model = m
        self.key = key
        self.key_old = key_old

        self.read_out()

    def __str__(self): # type: () -> str
        l = []
        if self.key_old is not None:
            l.append('old state:')
            l.append(Model._state_str(self.old_const_interps, self.old_rel_interps))
            l.append('\nnew state:')
        l.append(Model._state_str(self.const_interps, self.rel_interps))

        return '\n'.join(l)

    @staticmethod
    def _state_str(Cs, Rs):
        # type: (Dict[syntax.ConstantDecl, str], Dict[syntax.RelationDecl, List[Tuple[List[str], bool]]]) -> str
        l = []
        for C in Cs:
            l.append('%s = %s' % (C.name, Cs[C]))

        for R in Rs:

            for tup, b in sorted(Rs[R]):
                l.append('%s%s(%s)' % ('' if b else '!', R.name, ','.join(tup)))

        return '\n'.join(l)

    def read_out(self): # type: () -> None
        def rename(s): # type: (str) -> str
            return s.replace('!val!', '')

        self.univs = {} # type: Dict[syntax.SortDecl, List[str]]
        assert self.prog.scope is not None
        for z3sort in self.z3model.sorts():
            sort = self.prog.scope.get_sort(str(z3sort))
            assert sort is not None
            self.univs[sort] = [rename(str(x)) for x in self.z3model.get_universe(z3sort)]

        self.rel_interps = {} # type: Dict[syntax.RelationDecl, List[Tuple[List[str], bool]]]
        self.const_interps = {} # type: Dict[syntax.ConstantDecl, str]

        if self.key_old is not None:
            self.old_rel_interps = {} # type: Dict[syntax.RelationDecl, List[Tuple[List[str], bool]]]
            self.old_const_interps = {} # type: Dict[syntax.ConstantDecl, str]

        for z3decl in self.z3model.decls():
            z3name = str(z3decl)
            if z3name.startswith(self.key):
                name = z3name[len(self.key)+1:]
                R = self.rel_interps
                C = self.const_interps
            elif self.key_old is not None and z3name.startswith(self.key_old):
                name = z3name[len(self.key_old)+1:]
                R = self.old_rel_interps
                C = self.old_const_interps
            else:
                name = z3name
                R = self.rel_interps
                C = self.const_interps


            decl, _ = self.prog.scope.get(name)
            assert not isinstance(decl, syntax.QuantifierExpr) and \
                not isinstance(decl, syntax.TransitionDecl)
            if decl is not None:
                if isinstance(decl, syntax.RelationDecl):
                    if len(decl.arity) > 0:
                        l = []
                        domains = [self.z3model.get_universe(z3decl.domain(i))
                                   for i in range(z3decl.arity())]
                        g = product(domains) # type: Iterable[List[z3.ExprRef]]
                        for row in g:
                            ans = self.z3model.eval(z3decl(*row))
                            l.append(([rename(str(col)) for col in row], bool(ans)))
                        assert decl not in R
                        R[decl] = l
                    else:
                        ans = self.z3model.eval(z3decl())
                        assert decl not in R
                        R[decl] = [([], bool(ans))]
                else:
                    assert isinstance(decl, syntax.ConstantDecl)
                    v = self.z3model.eval(z3decl()).decl().name()
                    assert decl not in C
                    C[decl] = rename(v)

    def as_diagram(self): # type: () -> Diagram
        assert self.key_old is None, 'diagram can only be generated from a 1-state model'
        # TODO: remove above assertion by supporting 2-state models

        vs = [] # type: List[syntax.SortedVar]
        conjs = []
        for sort in self.univs:
            vs.extend(syntax.SortedVar(None, v, syntax.UninterpretedSort(None, sort.name))
                      for v in self.univs[sort])

            u = [syntax.Id(None, s) for s in self.univs[sort]]
            for i, a in enumerate(u):
                for b in u[i+1:]:
                    conjs.append(syntax.Neq(a, b))
        for R in self.rel_interps:
            for tup, ans in self.rel_interps[R]:
                if len(tup) > 0:
                    e = syntax.AppExpr(None, R.name, [syntax.Id(None, col) for col in tup]) # type: syntax.Expr

                else:
                    e = syntax.Id(None, R.name)
                e = e if ans else syntax.Not(e)
                conjs.append(e)
        for C in self.const_interps:
            e = syntax.Eq(syntax.Id(None, C.name), syntax.Id(None, self.const_interps[C]))
            conjs.append(e)


        diag = Diagram(vs, conjs)
        assert self.prog.scope is not None
        diag.resolve(self.prog.scope)

        return diag

def generalize_diag(s, prog, diag, f):
    # type: (z3.Solver, syntax.Program, Diagram, Set[syntax.Expr]) -> None
    logging.debug('generalizing diagram')
    logging.debug(str(diag))

    i = 0
    while i < len(diag.conjuncts):
        c = diag.remove_clause(i)
        if check_two_state_implication_all_transitions(s, prog, f, syntax.Not(diag.to_ast())) is not None:
            diag.add_clause(i, c)
            i += 1
        else:
            logging.debug('eliminated clause %s' % c)

    diag.prune_unused_vars()

    logging.debug('generalized diag')
    logging.debug(str(diag))

def find_predecessor(s, prog, pre_frames, diag):
    # type: (z3.Solver, syntax.Program, Set[syntax.Expr], Diagram) -> Tuple[z3.CheckSatResult, Union[Set[int], Tuple[syntax.TransitionDecl, Diagram]]]

    core = set() # type: Set[int]
    with s:
        for f in pre_frames:
            s.add(f.to_z3('old'))

        s.add(diag.to_z3('new'))

        for t in prog.transitions():
            logging.debug('checking %s' % t.name)
            with s:
                s.add(t.to_z3('new', 'old'))
                res = s.check(*diag.trackers)

                if res != z3.unsat:
                    logging.debug('found predecessor via %s' % t.name)
                    m = Model(prog, s.model(), 'old')
                    logging.debug(str(m))
                    return (res, (t, m.as_diagram()))
                else:
                    uc = s.unsat_core()
                    # logging.debug('uc')
                    # logging.debug(str(uc))

                    res = s.check(*[diag.trackers[i] for i in core])
                    if res == z3.unsat:
                        logging.debug('but existing core sufficient, skipping')
                        continue

                    for x in uc:
                        assert isinstance(x, z3.ExprRef)
                        core.add(int(x.decl().name()[1:]))

    return (z3.unsat, core)


def block(s, prog, fs, diag, j, trace, safety_goal=True):
    # type: (z3.Solver, syntax.Program, List[Set[syntax.Expr]], Diagram, int, List[Tuple[syntax.TransitionDecl, Diagram]], bool) -> bool
    if j == 0: # or (j == 1 and sat(init and diag)
        if safety_goal:
            print(trace)
            raise Exception('abstract counterexample')
        else:
            logging.debug('failed to block diagram')
            logging.debug(str(diag))
            return False

    # print fs
    while True:
        logging.debug('blocking diagram in frame %s' % j)
        logging.debug(str(diag))

        logging.debug('frame %d is' % (j-1))
        logging.debug('\n'.join(str(x) for x in fs[j-1]))
        res, x = find_predecessor(s, prog, fs[j-1], diag)
        if res == z3.unsat:
            logging.debug('no predecessor: blocked!')
            assert isinstance(x, set)
            core = x # type: Set[int]
            break
        assert isinstance(x, tuple), (res, x)
        trans, pre_diag = x

        trace.append(x)
        if not block(s, prog, fs, pre_diag, j-1, trace, safety_goal):
            return False
        trace.pop()

    logging.debug('core')
    logging.debug(str(core))

    # TODO: now use core

    logging.debug('unminimized diag')
    logging.debug(str(diag))

    diag.minimize_from_core(core)

    generalize_diag(s, prog, diag, fs[j-1])

    e = syntax.Not(diag.to_ast())

    logging.debug('minimized negated clause')
    logging.debug(str(e))

    for i in range(j+1):
        fs[i].add(e)

    return True

def check_inductive_frames(s, fs): # type: (z3.Solver, List[Set[syntax.Expr]]) -> Optional[Set[syntax.Expr]]
    for i in range(len(fs) - 1):
        if check_implication(s, fs[i+1], fs[i]) is None:
            return fs[i+1]
    return None



def push_forward_frames(s, prog, fs): # type: (z3.Solver, syntax.Program, List[Set[syntax.Expr]]) -> None
    for i, f in enumerate(fs[:-1]):
        logging.debug('pushing in frame %d' % i)

        for c in copy.copy(f):
            if c in fs[i+1]:
                continue
            m = check_two_state_implication_all_transitions(s, prog, f, c)
            if m is None:
                logging.debug('managed to push %s' % c)
                fs[i+1].add(c)
            else:
                diag = Model(prog, m, 'old').as_diagram()
                block(s, prog, fs, diag, i, [], False)


def simplify_frames(s, fs): # type: (z3.Solver, List[Set[syntax.Expr]]) -> None
    for i, f in enumerate(fs):
        logging.debug('simplifying frame %d' % i)
        to_consider = copy.copy(f)
        while to_consider:
            c = to_consider.pop()
            if check_implication(s, f - {c}, {c}) is None:
                logging.debug('removed %s' % c)
                f.remove(c)

def updr(s, prog, args): # type: (z3.Solver, syntax.Program, argparse.Namespace) -> Set[syntax.Expr]
    assert prog.scope is not None

    check_init(s, prog)

    if args.safety is not None:
        the_inv = None # type: Optional[syntax.InvariantDecl]
        for inv in prog.invs():
            if inv.name == args.safety:
                the_inv = inv
        if the_inv is None:
            raise Exception('No safety invariant named %s' % args.safety)
        safety = {the_inv.expr} # type: Set[syntax.Expr]
    else:
        safety = {inv.expr for inv in prog.invs()}



    fs = [set(init.expr for init in prog.inits())] # type: List[Set[syntax.Expr]]
    fs.append({syntax.Bool(None, True)})

    while True:
        logging.info('considering frame %s' % (len(fs) - 1,))

        m = check_implication(s, fs[-1], safety)
        if m is None:
            f = check_inductive_frames(s, fs)
            if f is not None:
                print('frame is safe and inductive. done!')
                print('\n'.join(str(x) for x in f))
                return f


            logging.info('frame is safe but not inductive. starting new frame')
            fs.append({syntax.Bool(None, True)})

            push_forward_frames(s, prog, fs)
            simplify_frames(s, fs)

            for i, f in enumerate(fs):
                logging.info('frame %d is\n%s' % (i, '\n'.join(str(x) for x in f)))
                logging.info('')

        else:
            logging.info('frame is not safe')
            mod = Model(prog, m, 'one')
            logging.debug(str(mod))
            d = mod.as_diagram()

            block(s, prog, fs, d, len(fs)-1, [])

        # find_predecessor(s, prog, fs[-2], d)

def debug_tokens(filename): # type: (str) -> None
    with open(filename) as f:
        parser.lexer.input(f.read())

    while True:
        tok = parser.lexer.token()
        if not tok: 
            break      # No more input
        print(tok)

def verify(s, prog, args): # type: (z3.Solver, syntax.Program, argparse.Namespace) -> None
    check_init(s, prog)
    check_transitions(s, prog)
    
    print('all ok!')

def parse_args(): # type: () -> argparse.Namespace
    argparser = argparse.ArgumentParser()

    argparser.add_argument('--log', default='WARNING')

    subparsers = argparser.add_subparsers()

    verify_subparser = subparsers.add_parser('verify')
    verify_subparser.set_defaults(main=verify)

    updr_subparser = subparsers.add_parser('updr')
    updr_subparser.add_argument('--safety')
    updr_subparser.set_defaults(main=updr)


    argparser.add_argument('filename')

    return argparser.parse_args()

def main(): # type: () -> None
    args = parse_args()

    logging.basicConfig(level=getattr(logging, args.log.upper(), None))

    with open(args.filename) as f:
        prog = parser.program_parser.parse(input=f.read(), filename=args.filename)

    prog.resolve()

    s = z3.Solver()
    for a in prog.axioms():
        s.add(a.expr.to_z3())

    args.main(s, prog, args)

if __name__ == '__main__':
    main()
