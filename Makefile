SHELL := /bin/bash

define TIMEFORMAT
	%R real,	%U user,	%S sys

endef
export TIMEFORMAT

PYTHON := python3 -u

MYPYVY_OPTS := --seed=0 --log=info --timeout 10000 --print-cmdline

SRC_FILES := $(shell find src -name '*.py' -not -name '*parsetab*' -not -path '*/ply/*')
PYV_FILES := $(sort $(wildcard examples/*.pyv))

test: check check-imports unit typecheck verify verify.cvc4 trace updr pd sep

gh-test: check check-imports unit typecheck verify trace updr sep

style:
	$(PYTHON) -m flake8 $(SRC_FILES) || true
	grep the_program $(SRC_FILES) || true

check:
	$(PYTHON) -m mypy --config-file ./mypy.ini $(SRC_FILES)
	@echo

check-imports: $(patsubst %.py, %.importable, $(SRC_FILES))

src/%.importable: src/%.py check
	@cd src; $(PYTHON) -c "import $(shell basename -s .py $<)" || { echo "file $< is not importable"; exit 1; }

unit: check check-imports
	$(PYTHON) -m unittest discover -s src -v
	@echo

prelude: check check-imports unit
	@echo ========================= Starting mypyvy tests =========================
	@echo

typecheck: $(patsubst %.pyv, %.typecheck, $(PYV_FILES))

verify: $(patsubst %.pyv, %.verify, $(PYV_FILES))

verify.cvc4: $(patsubst %.pyv, %.verify.cvc4, $(PYV_FILES))

trace: $(patsubst %.pyv, %.trace, $(PYV_FILES))

updr: examples/lockserv.updr examples/sharded_kv.updr

runmypyvy = time ( $(PYTHON) src/mypyvy.py $(1) $(MYPYVY_OPTS) $(2) > $(3).out && \
                   echo $$'\n'`head -n 1 $(3).out`$$'\n'`tail -n 1 $(3).out` )

runmypyvy_grep = time ( $(PYTHON) src/mypyvy.py $(1) $(MYPYVY_OPTS) $(2) > $(3).out && \
                        echo $$'\n'`head -n 1 $(3).out` && \
                        grep $(4) $(3).out )

%.typecheck: %.pyv prelude
	$(PYTHON) src/mypyvy.py typecheck $(MYPYVY_OPTS) $< > $@.out
	@#curl -s -H 'Content-Type: application/json' -X POST -d "{\"filename\": \"$<\"}" http://localhost:5000/typecheck | jq -e .success

%.verify: %.pyv prelude
	$(call runmypyvy, verify --exit-0, $<, $@)
	@# curl -s -H 'Content-Type: application/json' -X POST -d "{\"filename\": \"$<\", \"options\": [\"--seed=0\", \"--timeout=10000\"]}" http://localhost:5000/verify | jq -e '.success or (has("reason") and (.reason == "Verification error" or .reason == "Verification returned unknown"))'

%.verify.cvc4: %.pyv prelude
	$(call runmypyvy, verify --exit-0 --cvc4, $<, $@)

%.trace: %.pyv prelude
	$(call runmypyvy, trace, $<, $@)

%.updr: %.pyv prelude
	$(call runmypyvy, updr, $<, $@)

pd: prelude
# primal-dual-houdini

# should take about 1 minute
	$(call runmypyvy_grep, \
	pd-primal-dual-houdini --clear-cache --no-restarts --no-all-subclauses --induction-width=1 --cpus 2, \
	examples/ring_leader_election_single_sort.pyv, \
	examples/ring_leader_election_single_sort.primal-dual-houdini, \
	"Proved safety!")

# should take about 2 minutes
	$(call runmypyvy_grep, \
	pd-primal-dual-houdini --clear-cache --no-restarts --no-all-subclauses --induction-width=1 --cpus 2, \
	examples/sharded_kv.pyv, \
	examples/sharded_kv.prima-dual-houdini, \
	"Fixed point of induction width reached without a safety proof!")

pd-long: prelude
# primal-dual-houdini for problems that take a long time

# should take about 6 minutes
	$(call runmypyvy_grep, \
	pd-primal-dual-houdini --clear-cache --no-restarts --no-all-subclauses --induction-width=1 --cpus 2, \
	examples/ring_leader_election.pyv, \
	examples/ring_leader_election.primal-dual-houdini, \
	"Proved safety!")

# can take upto 2 hours
	$(call runmypyvy_grep, \
	pd-primal-dual-houdini --clear-cache --no-restarts --no-all-subclauses --induction-width=1 --cpus 2, \
	examples/toy_leader_consensus_forall.pyv, \
	examples/toy_leader_consensus_forall.primal-dual-houdini, \
	"Proved safety!")

# can take a few hours
	$(call runmypyvy_grep, \
	pd-primal-dual-houdini --clear-cache --no-restarts --no-all-subclauses --induction-width=1 --cpus 2, \
	examples/lockserv.pyv, \
	examples/lockserv.primal-dual-houdini, \
	-E "Proved safety!$|Fixed point of induction width reached without a safety proof!$")

sep: \
	examples/ring_leader_election.sep \
	examples/ring_leader_election_single_sort.sep \
	examples/lockserv.sep \
	examples/toy_leader_consensus_forall.sep \

%.sep: %.pyv prelude
	time ( $(PYTHON) src/mypyvy.py sep $(MYPYVY_OPTS) $< > $@.out && \
		echo && head -n 1 $@.out && \
		grep "Successfully learned a total" $@.out )

nightly:
	python3 script/nightly.py

clear-cache:
	rm -iv examples/*.cache

clean:
	rm -fv examples/*.out
	rm -fr .mypy_cache/

.PHONY: style check run test verify verify-pd updr bench typecheck trace pd pd-old pd-long unit check-imports clear-cache nightly clean prelude gh-test
