import z3
import sys
from typing import List, Any, Optional, Callable

z3.Forall = z3.ForAll # type: ignore

z3.init('/Users/jrw12/build/z3/build/')

def solver_enter(self):
    self.push()

def solver_exit(self, exn_type, exn_value, traceback):
    self.pop()

z3.Solver.__enter__ = solver_enter # type: ignore
z3.Solver.__exit__ = solver_exit # type: ignore

import parser, ast

def check_unsat(s): # type: (z3.Solver) -> None
    # print s.to_smt2()

    res = s.check()

    if res != z3.unsat:
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
                    (inv.name.value if inv.name.type == 'ID' else 'on line %s' % inv.name.lineno,),

                check_unsat(s)



def check_transitions(s, prog): # type: (z3.Solver, ast.Program) -> None
    with s:
        for inv in prog.invs():
            s.add(inv.expr.to_z3('old'))

        for t in prog.transitions():
            print 'checking transation %s:' % (t.name.value,)

            with s:
                s.add(t.to_z3('new', 'old'))
                for inv in prog.invs():
                    with s:
                        s.add(z3.Not(inv.expr.to_z3('new')))

                        print '  preserves invariant %s...' % \
                            (inv.name.value if inv.name.type == 'ID' else 'on line %s' % inv.name.lineno,),
                        sys.stdout.flush()

                        check_unsat(s)

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
        prog = parser.parser.parse(f.read())

    prog.resolve()

    s = z3.Solver()
    for a in prog.axioms():
        s.add(a.expr.to_z3())

    check_init(s, prog)
    check_transitions(s, prog)

    print 'all ok!'

if __name__ == '__main__':
    main()
