# mypyvy [![Build Status](https://travis-ci.org/wilcoxjay/mypyvy.svg?branch=master)](https://travis-ci.org/wilcoxjay/mypyvy)

A language for symbolic transition systems, inspired by Ivy.

## Dependencies

You need python version 3.8. Any version of the form 3.8.X should work.

```
python3.8 --version
Python 3.8.2
```

Make sure z3 is installed and on your `PYTHONPATH`. Basic functionality should
work with any version from the past few years, but for best results, use a recent
release, such as 4.8.7.

```
z3 --version
Z3 version 4.8.7 - 64 bit
```

Importing z3 should work (not report any errors) as follows.

```
python3.8
...
>>> import z3
>>>
```

You need all the python packages given in `requirements.txt`, which you can
do by running the following:

```
python3.8 -m pip install -r requirements.txt
```

You may wish to set up a virtual environment if you're into that.

## Getting started

mypyvy takes an input file describing a symbolic transition system and can
perform various tasks such as inductive invariant checking and inference.  For
an example input, see `examples/lockserv.pyv`, which is written in an tutorial
style.

For users who are familiar with Ivy, the syntax of mypyvy is broadly similar to
Ivy.  The primary difference is that transitions are specified directly as a
double-vocabulary formula, using `old(R(x))` to refer to the pre-state version
of relation `R`.

The mypyvy command line tool has several modes, all of which take a single `.pyv`
file.  See `mypyvy --help` for a list of modes and `mypyvy <mode> --help` for
a description of all command line options to a particular mode.
- `verify`: verifies that the invariants given in the file are inductive.
  For example, we can verify the lock service:
```
python3.8 src/mypyvy.py verify examples/lockserv.pyv
checking init:
  implies invariant mutex... ok. (0:00:00.000176)
  ...
checking transation send_lock:
  preserves invariant mutex... ok. (0:00:00.000120)
  preserves invariant on line 109... ok. (0:00:00.000107)
  ...
...
all ok!
```

  The `all ok!` message means success. If you delete one of the invariants and run again,
  you can see what the counterexamples look like.

- `updr`: search for a strengthening that proves the safety property.  For
  example, we can ask it to strengthen the mutex property of the lock service:

```
python3.8 src/mypyvy.py updr examples/lockserv.pyv
checking init:
  implies invariant mutex... ok. (0:00:00.000234)
frame is safe and inductive. done!
!(exists node0:node, node1:node. node0 != node1 & holds_lock(node0) & holds_lock(node1))
!(exists node0:node, node1:node. grant_msg(node1) & holds_lock(node0))
!(exists node0:node. holds_lock(node0) & server_holds_lock)
!(exists node0:node, node1:node. node0 != node1 & grant_msg(node0) & grant_msg(node1))
!(exists node0:node. grant_msg(node0) & server_holds_lock)
!(exists node0:node, node1:node. holds_lock(node0) & unlock_msg(node1))
!(exists node0:node, node1:node. grant_msg(node0) & unlock_msg(node1))
!(exists node0:node, node1:node. node0 != node1 & unlock_msg(node0) & unlock_msg(node1))
!(exists node0:node. server_holds_lock & unlock_msg(node0))
```

  The message `frame is safe and inductive. done!` means success, and then it
  prints out the inductive strengthening.  Note that even though the file
  `examples/lockserv.pyv` actually already contains an inductive invariant to prove
  `mutex`, the algorithm *does not* use the given strengthening, but looks only
  at `mutex`, which is marked as a `safety` property.  (You can see this by
  going and deleting all the other invariants in the file and re-running.)

- `bmc`: performs bounded model checking out to depth given by the `--depth=DEPTH`
  flag for a property given by the `--safety=NAME` flag. For example, we can check
  that `mutex` property is true for 5 steps as follows:
```
python3.8 src/mypyvy.py bmc --depth=5 --safety=mutex examples/lockserv.pyv
bmc checking the following property to depth 5
  forall N1:node, N2:node. holds_lock(N1) & holds_lock(N2) -> N1 = N2
ok. (0:00:00.062531)
```

  The `ok.` message means success.

  As another example, you could add the (false) invariant
```
invariant [bad] !holds_lock(N)
```
  to the file and then rerun.  `mypyvy` reports a counterexample trace demonstrating
  how to reach a state that violates the invariant. (Note the use of the option
  `--minimize-models` to find the trace with the fewest client nodes.)

```
python3.8 src/mypyvy.py bmc --depth=5 --safety=bad --minimize-models examples/lockserv.pyv
bmc checking the following property to depth 5
  forall N:node. !holds_lock(N)

sort node
  node0


state 0:
server_holds_lock()

transition send_lock

state 1:
lock_msg(node0)
server_holds_lock()

transition recv_lock

state 2:
grant_msg(node0)

transition send_lock

state 3:
grant_msg(node0)
lock_msg(node0)

transition stutter

state 4:
grant_msg(node0)
lock_msg(node0)

transition recv_grant

state 5:
holds_lock(node0)
lock_msg(node0)
error: found concrete trace violating safety
```

  The `error: ...` message means that a counterexample was found.  The trace is
  pretty readable!

- `theorem`: proves state-independent theorems about the background axioms of a model.
  Currently not documented and rarely used.

- `trace`: is an generalization of `bmc` that allows user-guided queries over executions.
  For example, at the bottom of the lockserv file, we see the following declaration:
```
sat trace {
  any transition
  any transition
  any transition
  assert exists N. holds_lock(N)
}
```

which asks mypyvy to find an execution with 3 steps that ends in a state where
some client holds the lock. (This is essentially the same query we used bmc to
answer above.)  A trace declaration says whether it is expected to be `sat` or
`unsat`, and mypyvy reports an error if it disagrees.  The syntax of trace queries
is under flux and currently undocumented.

- `typecheck`: This mode justs typechecks the input file and then exits. It is
  used by the emacs mode when the system's verification queries get too expensive
  to run on every keystroke.
