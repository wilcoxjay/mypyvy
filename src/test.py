import unittest

import utils
import parser
import syntax
import mypyvy

import os
from pathlib import Path
import shlex
import subprocess

from typing import List

PROJECT_ROOT = Path(__file__).resolve().parent.parent

class SyntaxTests(unittest.TestCase):
    def setUp(self) -> None:
        utils.args = mypyvy.parse_args(['typecheck', 'MOCK_FILENAME.pyv'])

    def test_as_clauses_basic(self) -> None:
        ios = [
            ('true', ['true | false']),
            ('foo', ['foo | false']),
            ('forall N1,N2. grant_msg(N1) & grant_msg(N2) -> N1 = N2',
             ['forall N1, N2. !grant_msg(N1) | !grant_msg(N2) | N1 = N2']),
            ('forall N1,N2. !(holds_lock(N1) & grant_msg(N2))',
             ['forall N1, N2. !holds_lock(N1) | !grant_msg(N2)']),
            ('forall N. !(unlock_msg(N) & server_holds_lock)',
             ['forall N. !unlock_msg(N) | !server_holds_lock']),
            ('!(exists N. holds_lock(N) & server_holds_lock)',
             ['forall N. !holds_lock(N) | !server_holds_lock']),
            ('!!(forall X. !(exists Y. (r(X) & s(Y)) & (q(X) & p(Y))))',
             ['forall X, Y. !r(X) | !s(Y) | !q(X) | !p(Y)']),
            ('forall X. r(X) & s(X)',
             ['forall X. r(X) | false', 'forall X. s(X) | false']),
            ('forall X. (r(X) | s(X)) & (q(X) | p(X))',
             ['forall X. r(X) | s(X)', 'forall X. q(X) | p(X)']),
        ]
        for expr, expected in ios:
            with self.subTest(expr=expr):
                clauses = syntax.as_clauses(parser.parse_expr(expr))
                # print(clause)
                self.assertEqual(clauses, [parser.parse_expr(expected_clause) for expected_clause in expected])

    def test_as_clauses_fail(self) -> None:
        egs = [
            'exists X. X = X',
        ]
        for expr in egs:
            with self.subTest(expr=expr):
                with self.assertRaises(Exception):
                    print(syntax.as_clauses(parser.parse_expr(expr)))

    def test_as_clauses_lockserv(self) -> None:
        with open(PROJECT_ROOT / 'examples' / 'lockserv.pyv') as f:
            prog = mypyvy.parse_program(f.read())
        prog.resolve()
        for inv in prog.invs():
            expr = inv.expr
            with self.subTest(expr=expr):
                syntax.as_clauses(expr)

    def test_consistent_hashing(self) -> None:
        with open(PROJECT_ROOT / 'examples' / 'lockserv.pyv') as f:
            prog1 = mypyvy.parse_program(f.read())
        with open(PROJECT_ROOT / 'examples' / 'lockserv.pyv') as f:
            prog2 = mypyvy.parse_program(f.read())

        prog1.resolve()
        prog2.resolve()
        for d1, d2 in zip(prog1.decls_containing_exprs(), prog2.decls_containing_exprs()):
            e1 = d1.expr
            e2 = d2.expr
            with self.subTest(msg='expr hash/eq', e1=e1, e2=e2):
                self.assertEqual(e1, e2)
                self.assertEqual(hash(e1), hash(e2))

    def test_relativize_quantifiers(self) -> None:
        minipaxos = '''
            sort node
            sort quorum
            immutable relation member(node, quorum)
            mutable relation active_node(node)
            mutable relation active_quorum(quorum)
        '''
        prog = mypyvy.parse_program(minipaxos)
        prog.resolve()
        node = prog.scope.get_sort('node')
        assert node is not None
        quorum = prog.scope.get_sort('quorum')
        assert quorum is not None
        active_node = prog.scope.get('active_node')
        assert isinstance(active_node, syntax.RelationDecl)
        active_quorum = prog.scope.get('active_quorum')
        assert isinstance(active_quorum, syntax.RelationDecl)
        guards = {node: active_node, quorum: active_quorum}

        e = parser.parse_expr('forall Q1, Q2. exists N. member(N, Q1) & member(N, Q2)')
        e.resolve(prog.scope, None)

        print(syntax.relativize_quantifiers(guards, e))


def build_python_cmd() -> List[str]:
    python = os.getenv('PYTHON') or 'python3.7'
    return [python, str((PROJECT_ROOT / 'src' / 'mypyvy.py').resolve())]

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
                python_cmd = build_python_cmd() + shlex.split(line) + [str(p)]
                with open(out_path, 'w') as f_out:
                    subprocess.run(python_cmd, stdout=f_out)
                diff_cmd = ['diff', '-uw', str(expect_path), str(out_path)]
                proc = subprocess.run(diff_cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                self.assertEqual(proc.returncode, 0, msg=f'{p} generated output {out_path} which differs from expected output {expect_path}.\n{" ".join(python_cmd)}\n{" ".join(diff_cmd)}')


class MonotoneFunctionTests(unittest.TestCase):
    def setUp(self) -> None:
        utils.args = mypyvy.parse_args(['typecheck', 'MOCK_FILENAME.pyv'])

    def test_mononte_function(self) -> None:
        from pd import MonotoneFunction
        elems: List[str] = []
        mf = MonotoneFunction([(elems,'+')])
        with self.assertRaises(Exception): mf[0]  # type: ignore
        with self.assertRaises(Exception): mf[0,]
        with self.assertRaises(Exception): mf[()]
        with self.assertRaises(Exception): mf[(),]  # type: ignore
        with self.assertRaises(Exception): mf[[],]  # type: ignore
        with self.assertRaises(Exception): mf[set(),]  # type: ignore
        self.assertIsNone(mf[frozenset(),])
        with self.assertRaises(Exception): mf[frozenset([0]),]
        with self.assertRaises(Exception): mf[frozenset([0,1]),]
        self.assertEqual( mf.seed([None]), (frozenset(),) )
        mf[frozenset(),] = False
        with self.assertRaises(Exception): mf[frozenset(),] = False
        with self.assertRaises(Exception): mf[frozenset(),] = True
        self.assertEqual( mf[frozenset(),], False )
        self.assertIsNone(mf.seed([None]))
        elems.append('hello')
        self.assertEqual( mf.seed([None]), (frozenset([0]),) )
        self.assertIsNone(mf.seed([{0: False}]))
        self.assertIsNone(mf[frozenset([0]),])
        with self.assertRaises(Exception): mf[frozenset([0,1]),]
        mf[frozenset([0]),] = False
        with self.assertRaises(Exception): mf[frozenset([0]),] = False
        with self.assertRaises(Exception): mf[frozenset([0]),] = True
        self.assertEqual( mf[frozenset([0]),], False )
        self.assertIsNone(mf.seed([None]))
        elems.append('world')
        self.assertIsNotNone(mf.seed([None]))
        self.assertIsNone(mf.seed([{1: False}]))
        mf[frozenset([1]),] = False
        self.assertEqual( mf.seed([None]), (frozenset([0,1]),) )
        mf[frozenset([0,1]),] = True
        self.assertEqual( mf[frozenset([0,1]),], True )
        self.assertIsNone(mf.seed([None]))
        elems.append('!')
        self.assertEqual( mf[frozenset([0,1,2]),], True )
        self.assertIsNone(mf[frozenset([0,2]),])
        self.assertIsNone(mf[frozenset([2]),])
        self.assertEqual(mf.to_elems((frozenset(),)), ([],))
        self.assertEqual(mf.to_elems((frozenset([0]),)), (['hello'],))
        self.assertEqual(mf.to_elems((frozenset([0,1]),)), (['hello', 'world'],))
        self.assertEqual(mf.to_elems((frozenset([1,0]),)), (['hello', 'world'],))
        self.assertEqual(mf.to_elems((frozenset([0,2]),)), (['hello', '!'],))
        with self.assertRaises(Exception): mf.to_elems((frozenset([3]),))

        mf = MonotoneFunction([(None, '+')])
        with self.assertRaises(Exception): mf[0]  # type: ignore
        with self.assertRaises(Exception): mf[frozenset(),]
        with self.assertRaises(Exception): mf[()]
        with self.assertRaises(Exception): mf[(),]  # type: ignore
        with self.assertRaises(Exception): mf[[],]  # type: ignore
        with self.assertRaises(Exception): mf[set(),]  # type: ignore
        self.assertIsNone(mf[0,])
        with self.assertRaises(Exception): mf[-1,]
        self.assertIsNone(mf.seed([(0,0)]))
        self.assertIsNone(mf.seed([(None,0)]))
        self.assertIsNotNone(mf.seed([(None,None)]))
        self.assertIsNotNone(mf.seed([(100,None)]))
        v = mf.seed([(100,200)])
        self.assertIsNotNone(v)
        assert v is not None
        k = v[0]
        self.assertIsInstance(k, int)
        self.assertLessEqual(100, k)
        self.assertLess(k, 200)
        self.assertIsNone(mf.seed([(5,5)]))
        self.assertEqual(mf.seed([(5,6)]), (5,))
        mf[5,] = False
        self.assertIsNone(mf.seed([(None,6)]))
        mf[50,] = True
        self.assertIsNone(mf.seed([(50,None)]))
        self.assertEqual(mf.seed([(None,7)]), (6,))
        self.assertEqual(mf.seed([(49,None)]), (49,))
        with self.assertRaises(Exception): mf[None,] = True
        with self.assertRaises(Exception): mf[None,] = False

        elems = []
        mf = MonotoneFunction([(elems,'-')])
        with self.assertRaises(Exception): mf[0]  # type: ignore
        with self.assertRaises(Exception): mf[0,]
        with self.assertRaises(Exception): mf[()]
        with self.assertRaises(Exception): mf[(),]  # type: ignore
        with self.assertRaises(Exception): mf[[],]  # type: ignore
        with self.assertRaises(Exception): mf[set(),]  # type: ignore
        self.assertIsNone(mf[frozenset(),])
        with self.assertRaises(Exception): mf[frozenset([0]),]
        with self.assertRaises(Exception): mf[frozenset([0,1]),]
        self.assertEqual( mf.seed([None]), (frozenset(),) )
        mf[frozenset(),] = True
        with self.assertRaises(Exception): mf[frozenset(),] = False
        with self.assertRaises(Exception): mf[frozenset(),] = True
        self.assertEqual( mf[frozenset(),], True )
        self.assertIsNone(mf.seed([None]))
        elems.append('hello')
        self.assertEqual( mf.seed([None]), (frozenset([0]),) )
        self.assertIsNone(mf.seed([{0: False}]))
        self.assertIsNone(mf[frozenset([0]),])
        with self.assertRaises(Exception): mf[frozenset([0,1]),]
        mf[frozenset([0]),] = True
        with self.assertRaises(Exception): mf[frozenset([0]),] = False
        with self.assertRaises(Exception): mf[frozenset([0]),] = True
        self.assertEqual( mf[frozenset([0]),], True )
        self.assertIsNone(mf.seed([None]))
        elems.append('world')
        self.assertIsNotNone(mf.seed([None]))
        self.assertIsNone(mf.seed([{1: False}]))
        mf[frozenset([1]),] = True
        self.assertEqual( mf.seed([None]), (frozenset([0,1]),) )
        mf[frozenset([0,1]),] = False
        self.assertEqual( mf[frozenset([0,1]),], False )
        self.assertIsNone(mf.seed([None]))
        elems.append('!')
        self.assertEqual( mf[frozenset([0,1,2]),], False )
        self.assertIsNone(mf[frozenset([0,2]),])
        self.assertIsNone(mf[frozenset([2]),])
        self.assertEqual(mf.to_elems((frozenset(),)), ([],))
        self.assertEqual(mf.to_elems((frozenset([0]),)), (['hello'],))
        self.assertEqual(mf.to_elems((frozenset([0,1]),)), (['hello', 'world'],))
        self.assertEqual(mf.to_elems((frozenset([1,0]),)), (['hello', 'world'],))
        self.assertEqual(mf.to_elems((frozenset([0,2]),)), (['hello', '!'],))
        with self.assertRaises(Exception): mf.to_elems((frozenset([3]),))

        # TODO: test multiple domains together, more tests with infinity
