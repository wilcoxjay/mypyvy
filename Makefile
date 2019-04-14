PYTHON := python3.7
MYPYVY_OPTS := --seed=0 --log=warning

check:
	$(PYTHON) -m mypy --config-file ./mypy.ini mypyvy.py

test: check verify updr

verify: check test/lockserv.verify test/consensus.verify test/sharded-kv.verify

updr: lockserv.updr sharded-kv.updr

bench:
	$(PYTHON) benchmark.py

%.verify: %.pyv
	time $(PYTHON) mypyvy.py verify $(MYPYVY_OPTS) $<

lockserv.updr:
	time $(PYTHON) mypyvy.py updr $(MYPYVY_OPTS) test/lockserv.pyv

sharded-kv.updr:
	time $(PYTHON) mypyvy.py updr $(MYPYVY_OPTS) test/sharded-kv.pyv

.PHONY: check run test verify updr bench lockserv.updr sharded-kv.updr
