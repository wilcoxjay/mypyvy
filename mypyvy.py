import z3
import sys
from typing import List, Any, Optional, Callable, Set, Tuple, Union, Iterable
import copy
import datetime
import logging

logging.basicConfig(level=logging.WARNING)

z3.Forall = z3.ForAll # type: ignore

z3.init('/Users/jrw12/build/z3/build/')

def solver_enter(self):
    self.push()

def solver_exit(self, exn_type, exn_value, traceback):
    self.pop()

z3.Solver.__enter__ = solver_enter # type: ignore
z3.Solver.__exit__ = solver_exit # type: ignore

import parser, ast

def _product(l, x, i):
    assert len(l) == len(x)

    if i >= len(l):
        yield x
    else:
        for y in l[i]:
            x[i] = y
            for z in _product(l, x, i+1):
                yield z

def product(l):
    x = [None for i in range(len(l))]
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

def check_unsat(s, prog): # type: (z3.Solver, ast.Program) -> None
    # print s.to_smt2()

    res = s.check()

    if res != z3.unsat:
        m = s.model()

        print ''
        print s.model()
        raise Exception('no')
    print 'ok.'

def check_init(s, prog): # type: (z3.Solver, ast.Program) -> None
    print 'checking init:'

    with s:
        for init in prog.inits():
            s.add(init.expr.to_z3('one'))

        for inv in prog.invs():
            with s:
                s.add(z3.Not(inv.expr.to_z3('one')))

                print '  implies invariant %s...' % \
                    (inv.name if inv.name is not None else 'on line %s' % inv.tok.lineno,),

                check_unsat(s, prog)


def check_transitions(s, prog): # type: (z3.Solver, ast.Program) -> None
    with s:
        for inv in prog.invs():
            s.add(inv.expr.to_z3('old'))

        for t in prog.transitions():
            print 'checking transation %s:' % (t.name,)

            with s:
                s.add(t.to_z3('new', 'old'))
                for inv in prog.invs():
                    with s:
                        s.add(z3.Not(inv.expr.to_z3('new')))

                        print '  preserves invariant %s...' % \
                            (inv.name if inv.name is not None else 'on line %s' % inv.tok.lineno,),
                        sys.stdout.flush()

                        check_unsat(s, prog)

def check_implication(s, hyps, concs):
    # type: (z3.Solver, Iterable[ast.Expr], Iterable[ast.Expr]) -> Optional[z3.ModelRef]
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
    # type: (z3.Solver, ast.Program, Iterable[ast.Expr], ast.Expr) -> Optional[z3.ModelRef]
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


def safe_resolve(e, scope, sort): # type: (ast.Expr, ast.Scope, ast.InferenceSort) -> None
    try:
        e.resolve(scope, sort)
    except Exception as exn:
        print 'internal error: tried to construct unresolvable intermediate expression'
        print e
        print exn
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

    def __init__(self, vs, conjuncts): # type: (List[ast.SortedVar], List[ast.Expr]) -> None
        self.vs = vs
        self.conjuncts = conjuncts
        self.q = ast.QuantifierExpr(None, 'EXISTS', vs, ast.And(*self.conjuncts))
        self.trackers = [] # type: List[z3.ExprRef]

    def __str__(self): # type: () -> str
        return 'exists %s.\n  %s' % (
            ', '.join(v.name for v in self.vs),
            ' &\n  '.join(str(c) for c in self.conjuncts)
        )

    def resolve(self, scope): # type: (ast.Scope) -> None
        safe_resolve(self.q, scope, ast.BoolSort)

    def to_z3(self, key): # type: (str) -> z3.ExprRef
        bs = []
        for sv in self.vs:
            n = sv.name
            assert sv.sort is not None and not isinstance(sv.sort, ast.SortInferencePlaceholder)
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

    def to_ast(self): # type: () -> ast.Expr
        if len(self.conjuncts) == 0:
            return ast.Bool(None, True)
        elif len(self.vs) == 0:
            return self.q.body
        else:
            return self.q

    def _reinit(self): # type: () -> None
        self.q.vs = self.vs
        self.q.body = ast.And(*self.conjuncts)
        self.q.binders = {}

    def minimize_from_core(self, core): # type: (Set[int]) -> None
        assert len(core) > 0

        self.conjuncts = [self.conjuncts[i] for i in core]
        self.prune_unused_vars()

    def remove_clause(self, i): # type: (int) -> ast.Expr
        c = self.conjuncts.pop(i)
        self._reinit()
        return c

    def add_clause(self, i, c): # type: (int, ast.Expr) -> None
        self.conjuncts.insert(i, c)
        self._reinit()

    def prune_unused_vars(self): # type: () -> None
        self.vs = [v for v in self.vs if any(c.contains_var(v.name) for c in self.conjuncts)]
        self._reinit()


def diagram_from_model(prog, m, key):
    # type: (ast.Program, z3.ModelRef, str) -> Diagram

    assert prog.scope is not None

    univs = {}
    d = {}
    l = []

    conjs = []

    for sort in m.sorts():
        u = m.get_universe(sort)
        # print ' ', sort, ': ', u

        ul = []
        for x in u:
            y = str(x).replace('!val!', '')
            ul.append(y)
            d[y] = x
            l.append((y, str(sort)))

        univs[sort] = ul

        for i in range(len(ul)):
            a = ul[i]
            for b in ul[i+1:]:
                conjs.append(ast.Neq(ast.Id(None, a), ast.Id(None, b)))

    for z3decl in m.decls():
        if str(z3decl).startswith(key):
            name = str(z3decl)[len(key)+1:]
        else:
            name = str(z3decl)

        decl = prog.scope.get(name)
        assert not isinstance(decl, ast.QuantifierExpr)
        if decl is not None:
            if isinstance(decl, ast.RelationDecl):
                if len(decl.arity) > 0:
                    for row in product([univs[z3decl.domain(i)] for i in range(z3decl.arity())]):
                        ans = m.eval(z3decl(*[d[col] for col in row]))
                        # print '%s(%s) = %s' % (decl.name, ', '.join(str(col) for col in row), ans)
                        app = ast.AppExpr(None, decl.name, [ast.Id(None, col) for col in row])
                        e = app if ans else ast.Not(app)

                        conjs.append(e)
                else:
                    ans = m.eval(z3decl())
                    const = ast.Id(None, decl.name)
                    e = const if ans else ast.Not(const)

                    conjs.append(e)
            else:
                assert isinstance(decl, ast.ConstantDecl)

                v = m.eval(z3decl()).decl().name()
                e = ast.Eq(ast.Id(None, decl.name), ast.Id(None, v.replace('!val!', '')))
                conjs.append(e)

    vs = [ast.SortedVar(None, v, ast.UninterpretedSort(None, s)) for v, s in l]

    diag = Diagram(vs, conjs)

    diag.resolve(prog.scope)

    return diag

def generalize_diag(s, prog, diag, f):
    # type: (z3.Solver, ast.Program, Diagram, Set[ast.Expr]) -> None
    logging.info('generalizing diagram')
    logging.info(str(diag))

    i = 0
    while i < len(diag.conjuncts):
        c = diag.remove_clause(i)
        if check_two_state_implication_all_transitions(s, prog, f, ast.Not(diag.to_ast())) is not None:
            diag.add_clause(i, c)
            i += 1
        else:
            logging.info('eliminated clause %s' % c)

    diag.prune_unused_vars()

    logging.info('generalized diag')
    logging.info(str(diag))

def find_predecessor(s, prog, pre_frames, diag):
    # type: (z3.Solver, ast.Program, Set[ast.Expr], Diagram) -> Tuple[z3.CheckSatResult, Union[Set[int], Tuple[ast.TransitionDecl, Diagram]]]

    core = set() # type: Set[int]
    with s:
        for f in pre_frames:
            s.add(f.to_z3('old'))

        s.add(diag.to_z3('new'))

        for t in prog.transitions():
            logging.info('checking %s' % t.name)
            with s:
                s.add(t.to_z3('new', 'old'))
                res = s.check(*diag.trackers)

                if res != z3.unsat:
                    logging.info('found predecessor via %s' % t.name)
                    m = s.model()
                    logging.info(str(m))
                    return (res, (t, diagram_from_model(prog, m, 'old')))
                else:
                    uc = s.unsat_core()
                    logging.info('uc')
                    logging.info(str(uc))

                    res = s.check(*[diag.trackers[i] for i in core])
                    if res == z3.unsat:
                        logging.info('but existing core sufficient, skipping')
                        continue

                    for x in uc:
                        assert isinstance(x, z3.ExprRef)
                        core.add(int(x.decl().name()[1:]))

    return (z3.unsat, core)


def block(s, prog, fs, diag, j, trace, safety_goal=True):
    # type: (z3.Solver, ast.Program, List[Set[ast.Expr]], Diagram, int, List[Tuple[ast.TransitionDecl, Diagram]], bool) -> bool
    if j == 0: # or (j == 1 and sat(init and diag)
        if safety_goal:
            print trace
            raise Exception('abstract counterexample')
        else:
            logging.info('failed to block diagram')
            logging.info(str(diag))
            return False

    # print fs
    while True:
        logging.info('blocking diagram in frame %s' % j)
        logging.info(str(diag))

        logging.info('frame %d is' % (j-1))
        logging.info('\n'.join(str(x) for x in fs[j-1]))
        res, x = find_predecessor(s, prog, fs[j-1], diag)
        if res == z3.unsat:
            logging.info('no predecessor: blocked!')
            assert isinstance(x, set)
            core = x # type: Set[int]
            break
        assert isinstance(x, tuple), (res, x)
        trans, pre_diag = x

        trace.append(x)
        if not block(s, prog, fs, pre_diag, j-1, trace, safety_goal):
            return False
        trace.pop()

    logging.info('core')
    logging.info(str(core))

    # TODO: now use core

    logging.info('unminimized diag')
    logging.info(str(diag))

    diag.minimize_from_core(core)

    generalize_diag(s, prog, diag, fs[j-1])

    e = ast.Not(diag.to_ast())

    logging.info('minimized negated clause')
    logging.info(str(e))

    for i in range(j+1):
        fs[i].add(e)

    return True

def check_inductive_frames(s, fs): # type: (z3.Solver, List[Set[ast.Expr]]) -> Optional[Set[ast.Expr]]
    for i in range(len(fs) - 1):
        if check_implication(s, fs[i+1], fs[i]) is None:
            return fs[i+1]
    return None



def push_forward_frames(s, prog, fs): # type: (z3.Solver, ast.Program, List[Set[ast.Expr]]) -> None
    for i, f in enumerate(fs[:-1]):
        logging.info('pushing in frame %d' % i)

        for c in copy.copy(f):
            m = check_two_state_implication_all_transitions(s, prog, f, c)
            if m is None:
                logging.info('managed to push %s' % c)
                fs[i+1].add(c)
            else:
                diag = diagram_from_model(prog, m, 'old')
                block(s, prog, fs, diag, i, [], False)


def simplify_frames(s, fs): # type: (z3.Solver, List[Set[ast.Expr]]) -> None
    for i, f in enumerate(fs):
        logging.info('simplifying frame %d' % i)
        to_consider = copy.copy(f)
        while to_consider:
            c = to_consider.pop()
            if check_implication(s, f - {c}, {c}) is None:
                logging.info('removed %s' % c)
                f.remove(c)

def updr(s, prog): # type: (z3.Solver, ast.Program) -> Set[ast.Expr]
    assert prog.scope is not None

    check_init(s, prog)

    safety = set([inv.expr for inv in prog.invs()]) # type: Set[ast.Expr]

    fs = [set(init.expr for init in prog.inits())] # type: List[Set[ast.Expr]]
    fs.append(set([ast.Bool(None, True)]))

    while True:
        print 'considering frame %s' % (len(fs) - 1,)

        m = check_implication(s, fs[-1], safety)
        if m is None:
            f = check_inductive_frames(s, fs)
            if f is not None:
                print 'frame is safe and inductive. done!'
                print '\n'.join(str(x) for x in f)
                return f


            print 'frame is safe but not inductive. starting new frame'
            fs.append(set([ast.Bool(None, True)]))

            push_forward_frames(s, prog, fs)
            simplify_frames(s, fs)

            for i, f in enumerate(fs):
                logging.info('frame %d is' % i)
                logging.info('\n'.join(str(x) for x in f))
                logging.info('')

        else:
            print 'frame is not safe'
            logging.info(str(m))
            d = diagram_from_model(prog, m, 'one')

            block(s, prog, fs, d, len(fs)-1, [])

        # find_predecessor(s, prog, fs[-2], d)





def debug_tokens(filename):
    with open(filename) as f:
        parser.lexer.input(f.read())

    while True:
        tok = parser.lexer.token()
        if not tok: 
            break      # No more input
        print(tok)

def verify(s, prog): # type: (z3.Solver, ast.Program) -> None
    check_init(s, prog)
    check_transitions(s, prog)
    
    print 'all ok!'


def main(): # type: () -> None
    if len(sys.argv) != 2:
        print 'Expected exactly one argument(filename)'
        sys.exit(1)

    filename = sys.argv[1]
    with open(filename) as f:
        prog = parser.parser.parse(f.read(), None, False, False, None, filename=filename)

    prog.resolve()

#    print repr(prog)
#    print prog

    s = z3.Solver()
    for a in prog.axioms():
        s.add(a.expr.to_z3())

    updr(s, prog)
    # verify(s, prog)

if __name__ == '__main__':
    main()
