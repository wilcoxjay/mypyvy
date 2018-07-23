import z3
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

def check_unsat(s):
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

                        check_unsat(s)

def main(): # type: () -> None
#     parser.lexer.input(open('tmp.pyv').read())
# 
#     while True:
#         tok = parser.lexer.token()
#         if not tok: 
#             break      # No more input
#         print(tok)


    prog = parser.parser.parse(open('lockserv.pyv').read())

    #print repr(prog)

    prog.resolve()

    #print repr(prog)

    s = z3.Solver()

    check_init(s, prog)
    check_transitions(s, prog)

    print 'all ok!'


if __name__ == '__main__':
    main()
