PYTHON := python3.7
MYPYVY_OPTS := --seed=0 --log=warning --timeout 2000

SRC_FILES := $(shell find src -name '*.py' -not -name '*parsetab*' -not -path '*/ply/*')

check:
	$(PYTHON) -m mypy --config-file ./mypy.ini $(SRC_FILES)

test: check check-imports unit typecheck verify trace updr pd

unit:
	$(PYTHON) -m unittest discover -s src -v

typecheck: $(patsubst %.pyv, %.typecheck, $(wildcard examples/*.pyv examples/*/*.pyv))

verify: examples/lockserv.verify examples/consensus.verify examples/sharded-kv.verify examples/oded/paxos_epr.verify examples/oded/paxos_forall.verify

trace: $(patsubst %.pyv, %.trace, $(wildcard examples/*.pyv))

updr: examples/lockserv.updr examples/sharded-kv.updr

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

pd:
	time $(PYTHON) src/mypyvy.py pd-forward-explore $(MYPYVY_OPTS) examples/lockserv_cnf.pyv # ~2s
	time $(PYTHON) src/mypyvy.py pd-repeated-houdini --sharp $(MYPYVY_OPTS) examples/lockserv.pyv # ~30s
	time $(PYTHON) src/mypyvy.py pd-repeated-houdini --no-sharp $(MYPYVY_OPTS) examples/lockserv.pyv # ~5m

check-imports: $(patsubst %.py, %.importable, $(SRC_FILES))

src/%.importable: src/%.py
	@cd src; $(PYTHON) -c "import $(shell basename -s .py $<)" || { echo "file $< is not importable"; exit 1; }

.PHONY: check run test verify updr bench typecheck trace pd unit check-imports
