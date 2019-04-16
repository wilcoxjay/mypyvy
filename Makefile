PYTHON := python3.7
MYPYVY_OPTS := --seed=0 --log=warning --timeout 2000

check:
	$(PYTHON) -m mypy --config-file ./mypy.ini src/mypyvy.py

test: check typecheck verify updr

typecheck: $(patsubst %.pyv, %.typecheck, $(wildcard test/*.pyv))

verify: check test/lockserv.verify test/consensus.verify test/sharded-kv.verify

updr: test/lockserv.updr test/sharded-kv.updr

bench:
	$(PYTHON) script/benchmark.py

%.typecheck: %.pyv
	$(PYTHON) src/mypyvy.py typecheck $(MYPYVY_OPTS) $<

%.verify: %.pyv
	time $(PYTHON) src/mypyvy.py verify $(MYPYVY_OPTS) $<

%.updr: %.pyv
	time $(PYTHON) src/mypyvy.py updr $(MYPYVY_OPTS) $<

.PHONY: check run test verify updr bench typecheck
