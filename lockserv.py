# this is an old file verifying the verdi lock service example directly on top of the
# python z3 api.

import z3
from typing import List, Callable

def unchanged(rnew,    # type: z3.FuncDeclRef
              rold     # type: z3.FuncDeclRef
           ):
    # type: (...) -> z3.ExprRef
    X = z3.Const('X', rnew.domain(0))
    return z3.Forall(X, rnew(X) == rold(X))

def remove(rnew,    # type: z3.FuncDeclRef
           rold,    # type: z3.FuncDeclRef
           x        # type: z3.ExprRef
           ):
    # type: (...) -> z3.ExprRef
    X = z3.Const('X', x.sort())
    return z3.Forall(X, rnew(X) == z3.And(rold(X), X != x))

def insert(rnew,    # type: z3.FuncDeclRef
           rold,    # type: z3.FuncDeclRef
           x        # type: z3.ExprRef
           ):
    # type: (...) -> z3.ExprRef
    X = z3.Const('X', x.sort())
    return z3.Forall(X, rnew(X) == z3.Or(rold(X), X == x))

node = z3.DeclareSort('node')

class Vocab(object):
    lock_msg = None # type: z3.FuncDeclRef
    grant_msg = None # type: z3.FuncDeclRef
    unlock_msg = None # type: z3.FuncDeclRef
    holds_lock = None # type: z3.FuncDeclRef
    server_holds_lock = None # type: z3.ExprRef

v1 = Vocab()
v1.lock_msg = z3.Function('lock_msg', node, z3.BoolSort())
v1.grant_msg = z3.Function('grant_msg', node, z3.BoolSort())
v1.unlock_msg = z3.Function('unlock_msg', node, z3.BoolSort())
v1.holds_lock = z3.Function('holds_lock', node, z3.BoolSort())
v1.server_holds_lock = z3.Const('server_holds_lock', z3.BoolSort())

v2 = Vocab()
v2.lock_msg = z3.Function('new_lock_msg', node, z3.BoolSort())
v2.grant_msg = z3.Function('new_grant_msg', node, z3.BoolSort())
v2.unlock_msg = z3.Function('new_unlock_msg', node, z3.BoolSort())
v2.holds_lock = z3.Function('new_holds_lock', node, z3.BoolSort())
v2.server_holds_lock = z3.Const('new_server_holds_lock', z3.BoolSort())

def init(v): # type: (Vocab) -> z3.ExprRef
    N = z3.Const('N', node)
    return z3.And(
        z3.Forall(N, z3.Not(v.lock_msg(N))),
        z3.Forall(N, z3.Not(v.grant_msg(N))),
        z3.Forall(N, z3.Not(v.unlock_msg(N))),
        z3.Forall(N, z3.Not(v.holds_lock(N))),
        v.server_holds_lock
    )

def safety(v): # type: (Vocab) -> z3.ExprRef
    N1, N2 = z3.Consts('N1 N2', node)
    return z3.Forall([N1, N2],
                     z3.Implies(
                         z3.And(v.holds_lock(N1), v.holds_lock(N2)),
                         N1 == N2
                     )
    )

def inv(v): # type: (Vocab) -> List[z3.ExprRef]
    N, N1, N2 = z3.Consts('N N1 N2', node)
    return [
        safety(v),
        z3.Forall([N1, N2], z3.Not(z3.And(v.grant_msg(N1), v.holds_lock(N2)))),
        z3.Forall([N1, N2], z3.Not(z3.And(v.unlock_msg(N1), v.holds_lock(N2)))),
        z3.Forall([N1, N2], z3.Not(z3.And(v.grant_msg(N1), v.unlock_msg(N2)))),
        z3.Forall([N1, N2], z3.Implies(z3.And(v.grant_msg(N1), v.grant_msg(N2)), N1 == N2)),
        z3.Forall([N1, N2], z3.Implies(z3.And(v.unlock_msg(N1), v.unlock_msg(N2)), N1 == N2)),
        z3.Forall(N, z3.Implies(v.holds_lock(N), z3.Not(v.server_holds_lock))),
        z3.Forall(N, z3.Implies(v.grant_msg(N), z3.Not(v.server_holds_lock))),
        z3.Forall(N, z3.Implies(v.unlock_msg(N), z3.Not(v.server_holds_lock)))
    ]

def send_lock(v1, v2): # type: (Vocab, Vocab) -> z3.ExprRef
    n = z3.Const('n', node)
    return z3.Exists(n,
                     z3.And(
                         insert(v2.lock_msg, v1.lock_msg, n),
                         unchanged(v2.grant_msg, v1.grant_msg),
                         unchanged(v2.holds_lock, v1.holds_lock),
                         unchanged(v2.unlock_msg, v1.unlock_msg),
                         v2.server_holds_lock == v1.server_holds_lock
                     )
    )

def recv_lock(v1, v2): # type: (Vocab, Vocab) -> z3.ExprRef
    n = z3.Const('n', node)
    return z3.Exists(n,
                     z3.And(
                         v1.lock_msg(n),
                         v1.server_holds_lock,
                         z3.Not(v2.server_holds_lock),
                         remove(v2.lock_msg, v1.lock_msg, n),
                         insert(v2.grant_msg, v1.grant_msg, n),
                         unchanged(v2.unlock_msg, v1.unlock_msg),
                         unchanged(v2.holds_lock, v1.holds_lock)
                     )
    )

def recv_grant(v1, v2): # type: (Vocab, Vocab) -> z3.ExprRef
    n = z3.Const('n', node)
    return z3.Exists(n,
                     z3.And(
                         v1.grant_msg(n),
                         remove(v2.grant_msg, v1.grant_msg, n),
                         insert(v2.holds_lock, v1.holds_lock, n),
                         unchanged(v2.lock_msg, v1.lock_msg),
                         unchanged(v2.unlock_msg, v1.unlock_msg),
                         v2.server_holds_lock == v1.server_holds_lock
                     )
    )

def unlock(v1, v2): # type: (Vocab, Vocab) -> z3.ExprRef
    n = z3.Const('n', node)
    return z3.Exists(n,
                     z3.And(
                         v1.holds_lock(n),
                         remove(v2.holds_lock, v1.holds_lock, n),
                         insert(v2.unlock_msg, v1.unlock_msg, n),
                         unchanged(v2.lock_msg, v1.lock_msg),
                         unchanged(v2.grant_msg, v1.grant_msg),
                         v2.server_holds_lock == v1.server_holds_lock
                     )
    )

def recv_unlock(v1, v2): # type: (Vocab, Vocab) -> z3.ExprRef
    n = z3.Const('n', node)
    return z3.Exists(n,
                     z3.And(
                         v1.unlock_msg(n),
                         remove(v2.unlock_msg, v1.unlock_msg, n),
                         v2.server_holds_lock,
                         unchanged(v2.lock_msg, v1.lock_msg),
                         unchanged(v2.grant_msg, v1.grant_msg),
                         unchanged(v2.holds_lock, v1.holds_lock)
                     )
    )



def check_transition(s, t): # type: (z3.Solver, Callable[[Vocab, Vocab], z3.ExprRef]) -> None
    print('checking transition %s' % t.__name__)
    with s:
        s.add(*inv(v1))
        s.add(t(v1, v2))
        for c in inv(v2):
            with s:
                print('  preserves clause %s...' % c, end=' ')
                s.add(z3.Not(c))
                if s.check() != z3.unsat:
                    print('')
                    print(s.model())
                    raise Exception('no')
                print(' ok.')
    print('transition %s ok.' % t.__name__)

def check_safety(s): # type: (z3.Solver) -> None
    with s:
        s.add(*inv(v1))
        s.add(z3.Not(safety(v1)))
        print('checking if inv implies safety...', end=' ')
        if s.check() != z3.unsat:
            print('')
            print(s.model())
            raise Exception('no')
        print(' ok.')

def check_init(s): # type: (z3.Solver) -> None
    with s:
        s.add(init(v1))
        s.add(z3.Not(z3.And(*inv(v1))))
        print('checking if init implies inv...', end=' ')
        if s.check() != z3.unsat:
            print('')
            print(s.model())
            raise Exception('no')
        print(' ok.')

def main(): # type: () -> None
    s = z3.Solver()
    check_safety(s)
    check_init(s)
    check_transition(s, send_lock)
    check_transition(s, recv_lock)
    check_transition(s, recv_grant)
    check_transition(s, unlock)
    check_transition(s, recv_unlock)

    print('all ok.')
