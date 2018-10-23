# mypyvy

My python reimplementation of (some of) Ivy.

## Setup dependencies

You need python version 3.7. (Sorry.)

```
python3 --version
Python 3.7.0
```

Make sure z3 is installed and on your `PYTHONPATH`. I use z3 version 4.7.1.

```
z3 --version
Z3 version 4.7.1 - 64 bit
```

Importing z3 should work (not report any errors) as follows.

```
python3
Python 3.7.0 (default, Oct 18 2018, 15:38:37)
[GCC 5.5.0] on linux
Type "help", "copyright", "credits" or "license" for more information.
>>> import z3
>>>
```

You need all the python packages given in `requirements.txt`, which you can
do by running the following:

```
pip3 install -r requirements.txt
```

## Getting started

mypyvy takes input files describing transition relations and performs various verification tasks.
For an example input, see `test/lockserv.pyv`, which is fairly well documented (though perhaps too documented...).

The syntax is broadly fairly similar to Ivy. The primary difference is that transitions are
specified directly as a double-vocabulary formula, using `old(R(x))` to refer to the
pre-state version of relation `R`.

The mypyvy command line tool has several modes, all of which take a single `.pyv` file.
- `verify`: verifies that the invariants given in the file are inductive.
  For example, we can verify the lock service:
```
python3 mypyvy.py verify test/lockserv.pyv
checking init:
  implies invariant mutex...ok. (0:00:00.001003)
  ...
checking transation send_lock:
  preserves invariant mutex...ok. (0:00:00.000653)
  preserves invariant on line 109...ok. (0:00:00.000651)
  ...
...
all ok!
```

  The `all ok!` message means success. If you delete one of the invariants and run again,
  you can see what the counterexamples look like.

- `updr`: search for a strengthening that proves the invariant named by the `--safety=NAME` flag.
  For example, we can ask it to strengthen the mutex property of the lock service:
```
python3 mypyvy.py updr --safet=mutex test/lockserv.pyv
checking init:
  implies invariant mutex...ok. (0:00:00.000541)
  implies invariant on line 109...ok. (0:00:00.000423)
  implies invariant on line 110...ok. (0:00:00.000407)
  implies invariant on line 112...ok. (0:00:00.000364)
  implies invariant on line 113...ok. (0:00:00.000342)
  implies invariant on line 114...ok. (0:00:00.000336)
  implies invariant on line 116...ok. (0:00:00.000309)
  implies invariant on line 117...ok. (0:00:00.000298)
  implies invariant on line 118...ok. (0:00:00.000296)
frame is safe and inductive. done!
forall N1:node, N2:node. holds_lock(N1) & holds_lock(N2) -> N1 = N2
!(exists node0:node, node1:node. grant_msg(node1) & holds_lock(node0))
!(exists node0:node. holds_lock(node0) & server_holds_lock)
!(exists node0:node, node1:node. node0 != node1 & grant_msg(node0) & grant_msg(node1))
!(exists node0:node. grant_msg(node0) & server_holds_lock)
!(exists node0:node, node1:node. holds_lock(node0) & unlock_msg(node1))
!(exists node0:node, node1:node. grant_msg(node0) & unlock_msg(node1))
!(exists node0:node, node1:node. node0 != node1 & unlock_msg(node0) & unlock_msg(node1))
!(exists node0:node. server_holds_lock & unlock_msg(node0))
```

  The message `frame is safe and inductive. done!` means success, and then it prints out
  the inductive strengthening. Note that even though the file `test/lockserv.pyv` actually
  already contains an inductive invariant to prove `mutex`, the algorithm *does not* use
  the given strengthening, but looks only at `mutex`. (You can see this by going and
  deleting all the other invariants in the file and re-running.)

- `bmc`: performs bounded model checking out to depth given by the `--depth=DEPTH` flag
  for a property given by the `--safety=NAME` flag.
  For example, we can check that `mutex` property is true for 5 steps as follows:
```
python3 mypyvy.py bmc --depth=5 --safety=mutex test/lockserv.pyv
bmc checking the following property to depth 5
  forall N1:node, N2:node. holds_lock(N1) & holds_lock(N2) -> N1 = N2
ok. (0:00:00.678835)
```

  The `ok.` message means success.

  As another example, you could add the (false) invariant
```
invariant [bad] !holds_lock(N)
```
  to the file and then rerun. You will get a (horribly ugly) counterexample from
  which it is possible to reconstruct a trace violating the property

```
python3 mypyvy.py bmc --depth=5 --safety=bad test/lockserv.pyv
bmc checking the following property to depth 5
  forall N:node. !holds_lock(N)

<horrible countermodel here>
...
no! (0:00:00.198516)
```

  The `no!` message means that a counterexample was found.

- `theorem`: proves state-independent theorems about the background axioms of a model.
  Currently not documented and rarely used.
