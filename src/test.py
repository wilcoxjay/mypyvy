import unittest

import parser
import syntax
import mypyvy

import os
from pathlib import Path
import shlex
import subprocess

PROJECT_ROOT = Path(__file__).resolve().parent.parent

class SyntaxTests(unittest.TestCase):
    def setUp(self) -> None:
        mypyvy.parse_args(['typecheck', 'MOCK_FILENAME.pyv'])

    def test_as_clause_basic(self) -> None:
        ios = [
            ('true', 'true'),
            ('foo', 'foo'),
            ('forall N1,N2. grant_msg(N1) & grant_msg(N2) -> N1 = N2',
             'forall N1, N2. !grant_msg(N1) | !grant_msg(N2) | N1 = N2'),
            ('forall N1,N2. !(holds_lock(N1) & grant_msg(N2))',
             'forall N1, N2. !holds_lock(N1) | !grant_msg(N2)'),
            ('forall N. !(unlock_msg(N) & server_holds_lock)',
             'forall N. !unlock_msg(N) | !server_holds_lock'),
            ('!(exists N. holds_lock(N) & server_holds_lock)',
             'forall N. !holds_lock(N) | !server_holds_lock'),
            ('!!(forall X. !(exists Y. (r(X) & s(Y)) & (q(X) & p(Y))))',
             'forall X, Y. !r(X) | !s(Y) | !q(X) | !p(Y)')
        ]
        for expr, expected in ios:
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

class RegressionTests(unittest.TestCase):
    def test_regressions(self) -> None:
        for p in sorted(Path(PROJECT_ROOT / 'examples' / 'regression').glob('*.pyv')):
            with self.subTest(testFile=str(p)):
                with open(p) as f:
                    line = f.readline()
                magic_prefix = '# MYPYVY: '
                assert line.startswith(magic_prefix)
                line = line[len(magic_prefix):]
                python = os.getenv('PYTHON') or 'python3.7'
                out_path = p.with_suffix('.output')
                expect_path = p.with_suffix('.expect')
                python_cmd = [python, str((PROJECT_ROOT / 'src' / 'mypyvy.py').resolve())] + shlex.split(line) + [str(p)]
                with open(out_path, 'w') as f_out:
                    subprocess.run(python_cmd, stdout=f_out)
                diff_cmd = ['diff', '-uw', str(expect_path), str(out_path)]
                proc = subprocess.run(diff_cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                self.assertEqual(proc.returncode, 0, msg=f'{p} generated output {out_path} which differs from expected output {expect_path}.\n{" ".join(python_cmd)}\n{" ".join(diff_cmd)}')
