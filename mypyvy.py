import z3
import sys
from typing import List, Any, Optional, Callable, Set, Tuple

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
    # type: (z3.Solver, Set[ast.Expr], Set[ast.Expr]) -> Optional[z3.ModelRef]
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

def safe_resolve(e, scope, sort):
    try:
        e.resolve(scope, sort)
    except Exception as exn:
        print 'internal error: tried to construct unresolvable intermediate expression'
        print e
        print exn
        raise e


def diagram_from_model(prog, m, key):
    # type: (ast.Program, z3.ModelRef, str) -> ast.Expr

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
            decl = prog.scope.get(str(z3decl)[len(key)+1:])
            assert not isinstance(decl, ast.QuantifierExpr)
            if decl is not None:
                assert isinstance(decl, ast.RelationDecl) # TODO: remove

                # print z3decl
                # print decl

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

    vs = [ast.SortedVar(None, v, ast.UninterpretedSort(None, s)) for v, s in l]
    q = ast.QuantifierExpr(None, 'EXISTS', vs, ast.And(*conjs))

    safe_resolve(q, prog.scope, None)

    return q

def find_predecessor(s, prog, pre_frames, diag):
    # type: (z3.Solver, ast.Program, Set[ast.Expr], ast.Expr) -> Optional[Tuple[ast.TransitionDecl, ast.Expr]]

    with s:
        for f in pre_frames:
            s.add(f.to_z3('old'))
        s.add(diag.to_z3('new'))

        for t in prog.transitions():
            print 'checking %s' % t.name
            with s:
                s.add(t.to_z3('new', 'old'))
                res = s.check()

                if res != z3.unsat:
                    print 'found predecessor via %s' % t.name
                    m = s.model()
                    print m
                    return (t, diagram_from_model(prog, m, 'old'))
    return None


def block(s, prog, fs, diag, j, trace):
    # type: (z3.Solver, ast.Program, List[Set[ast.Expr]], ast.Expr, int, List[Tuple[ast.TransitionDecl, ast.Expr]]) -> None
    if j == 0: # or (j == 1 and sat(init and diag)
        print trace
        raise Exception('abstract counterexample')

    # print fs
    while True:
        print 'blocking diagram in frame %s' % j
        print diag

        print fs[j-1]
        x = find_predecessor(s, prog, fs[j-1], diag)
        if x is None:
            print 'no predecessor: blocked!'
            break
        trans, pre_diag = x

        trace.append(x)
        block(s, prog, fs, pre_diag, j-1, trace)
        trace.pop()

    for i in range(j+1):
        fs[i].add(ast.Not(diag))


def updr(s, prog): # type: (z3.Solver, ast.Program) -> Set[ast.Expr]
    assert prog.scope is not None

    check_init(s, prog)

    safety = set([inv.expr for inv in prog.invs()]) # type: Set[ast.Expr]

    fs = [set(init.expr for init in prog.inits())] # type: List[Set[ast.Expr]]
    fs.append(set([ast.Bool(None, True)]))

    while True:
        print 'considering frame %s' % len(fs)

        if fs[-1] <= fs[-2]:
            return fs[-1]

        m = check_implication(s, fs[-1], safety)
        if m is None:
            print 'frame is safe, starting new frame'
            fs.append(set([ast.Bool(None, True)]))
        else:
            print 'frame is not safe'
            print m
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

def main(): # type: () -> None
    if len(sys.argv) != 2:
        print 'Expected exactly one argument(filename)'
        sys.exit(1)

    filename = sys.argv[1]
    with open(filename) as f:
        prog = parser.parser.parse(f.read(), None, False, False, None, filename=filename)

    prog.resolve()

    print repr(prog)
    print prog

#     s = z3.Solver()
#     for a in prog.axioms():
#         s.add(a.expr.to_z3())
# 
#     updr(s, prog)
    # check_init(s, prog)
    # check_transitions(s, prog)
    # 
    # print 'all ok!'

if __name__ == '__main__':
    main()
