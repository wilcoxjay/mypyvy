PYTHON := python3
MYPYVY_OPTS := --seed=0 --log=warning

check:
	MYPYPATH=stubs mypy --strict --disallow-untyped-defs mypyvy.py unittest.py

test: check unittest verify updr

unittest:
	$(PYTHON) unittest.py

verify: check lockserv.verify consensus.verify sharded-kv.verify

updr: lockserv.updr consensus.updr sharded-kv.updr

bench:
	$(PYTHON) benchmark.py

%.verify: %.pyv
	time $(PYTHON) mypyvy.py $(MYPYVY_OPTS) verify $<

lockserv.updr:
	time $(PYTHON) mypyvy.py $(MYPYVY_OPTS) updr --safety=mutex lockserv.pyv

consensus.updr:
	time $(PYTHON) mypyvy.py $(MYPYVY_OPTS) updr --safety=one_leader consensus.pyv

sharded-kv.updr:
	time $(PYTHON) mypyvy.py $(MYPYVY_OPTS) updr --safety=keys_unique sharded-kv.pyv

.PHONY: check run unittest test verify updr bench lockserv.updr consensus.updr sharded-kv.updr
