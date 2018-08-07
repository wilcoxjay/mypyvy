import mypyvy
import parser
import syntax

import sys

scope = syntax.Scope()
scope.add_sort(None, 'T', syntax.SortDecl(None, 'T'))
scope.get_sort('T')

e1 = parser.expr_parser.parse(input='forall x:T. x = x')
e2 = parser.expr_parser.parse(input='forall x:T. x = x')
e3 = parser.expr_parser.parse(input='forall x:T. x != x')
e4 = parser.expr_parser.parse(input='forall y:T. y = y')

e1.resolve(scope, None)
e2.resolve(scope, None)
e3.resolve(scope, None)
e4.resolve(scope, None)

any_failed = False

def _fail(msg: str) -> None:
    global any_failed
    print('test failed: %s' % msg)
    any_failed = True

def _pass() -> None:
    print('test passed')

def assertEqual(x: object, y: object) -> None:
    if not (x == y):
        _fail('expected %s == %s, but reported not equal' % (repr(x), repr(y)))
    else:
        _pass()

def assertNotEqual(x: object, y: object) -> None:
    if not (x != y):
        _fail('expected %s != %s, but reported equal' % (repr(x), repr(y)))
    else:
        _pass()

assertEqual(e1, e2)
assertEqual(hash(e1), hash(e2))
assertNotEqual(e1, e3)
assertEqual(e1, e4)
assertEqual(hash(e1), hash(e4))
assertNotEqual(e3, e4)

if any_failed:
    sys.exit(1)
