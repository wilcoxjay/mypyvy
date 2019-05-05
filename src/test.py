import unittest

import parser
import syntax
import pd
import mypyvy

from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent

class SyntaxTests(unittest.TestCase):
    def setUp(self) -> None:
        mypyvy.parse_args(['typecheck', 'MOCK_FILENAME.pyv'])

    def test_as_clause_basic(self) -> None:
        ios = [
            ('true', 'true'),
            ('foo', 'foo'),
            ('forall N1,N2. grant_msg(N1) & grant_msg(N2) -> N1 = N2', 'forall N1, N2. !grant_msg(N1) | !grant_msg(N2) | N1 = N2'),
            ('forall N1,N2. !(holds_lock(N1) & grant_msg(N2))', 'forall N1, N2. !holds_lock(N1) | !grant_msg(N2)'),
            ('forall N. !(unlock_msg(N) & server_holds_lock)', 'forall N. !unlock_msg(N) | !server_holds_lock'),
            ('!(exists N. holds_lock(N) & server_holds_lock)', 'forall N. !holds_lock(N) | !server_holds_lock'),
            ('!!(forall X. !(exists Y. (r(X) & s(Y)) & (q(X) & p(Y))))', 'forall X, Y. !r(X) | !s(Y) | !q(X) | !p(Y)')
        ]
        for expr,expected in ios:
            with self.subTest(expr=expr):
                clause = syntax.as_clause(parser.parse_expr(expr))
                # print(clause)
                self.assertEqual(clause, parser.parse_expr(expected))

    def test_as_clause_lockserv(self) -> None:
        with open(PROJECT_ROOT / 'examples' / 'lockserv.pyv') as f:
            prog = mypyvy.parse_program(f.read())
        prog.resolve()
        for inv in prog.invs():
            expr = inv.expr
            with self.subTest(expr=expr):
                syntax.as_clause(expr)
