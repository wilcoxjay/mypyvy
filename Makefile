PYTHON := python3.7
MYPYVY_OPTS := --seed=0 --log=warning --timeout 2000  --minimize-models

check:
	$(PYTHON) -m mypy --config-file ./mypy.ini src/mypyvy.py

test: check typecheck verify trace updr

typecheck: $(patsubst %.pyv, %.typecheck, $(wildcard test/*.pyv))

verify: test/lockserv.verify test/consensus.verify test/sharded-kv.verify

trace: $(patsubst %.pyv, %.trace, $(wildcard test/*.pyv))

updr: test/lockserv.updr test/sharded-kv.updr

bench:
	$(PYTHON) script/benchmark.py

%.typecheck: %.pyv
	$(PYTHON) src/mypyvy.py typecheck $(MYPYVY_OPTS) $<

%.trace: %.pyv
	$(PYTHON) src/mypyvy.py trace $(MYPYVY_OPTS) $<

%.verify: %.pyv
	time $(PYTHON) src/mypyvy.py verify $(MYPYVY_OPTS) $<

%.updr: %.pyv
	time $(PYTHON) src/mypyvy.py updr $(MYPYVY_OPTS) $<

.PHONY: check run test verify updr bench typecheck trace
