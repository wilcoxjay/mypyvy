SHELL := /bin/bash

define TIMEFORMAT
	%R real,	%U user,	%S sys

endef
export TIMEFORMAT

PYTHON := python3.8 -u

MYPYVY_OPTS := --seed=0 --log=info --timeout 60000 --print-cmdline

SRC_FILES := $(shell find src -name '*.py' -not -name '*parsetab*' -not -path '*/ply/*')

test: check check-imports unit typecheck verify verify.cvc4 trace updr pd-old pd sep

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

typecheck: $(patsubst %.pyv, %.typecheck, $(wildcard examples/*.pyv examples/*/*.pyv))

verify: $(patsubst %.pyv, %.verify, $(sort $(wildcard examples/*.pyv examples/*/*.pyv)))

verify.cvc4: $(patsubst %.pyv, %.verify.cvc4, $(sort $(wildcard examples/*.pyv examples/*/*.pyv)))

trace: $(patsubst %.pyv, %.trace, $(wildcard examples/*.pyv))

updr: examples/lockserv.updr examples/sharded-kv.updr

runmypyvy = time ( $(PYTHON) src/mypyvy.py $(1) $(MYPYVY_OPTS) $(2) > $(3).out && \
                   echo $$'\n'`head -n 1 $(3).out`$$'\n'`tail -n 1 $(3).out` )

runmypyvy_grep = time ( $(PYTHON) src/mypyvy.py $(1) $(MYPYVY_OPTS) $(2) > $(3).out && \
                        echo $$'\n'`head -n 1 $(3).out` && \
                        grep $(4) $(3).out )

%.typecheck: %.pyv prelude
	$(PYTHON) src/mypyvy.py typecheck $(MYPYVY_OPTS) $< > $@.out

%.verify: %.pyv prelude
	$(call runmypyvy, verify --exit-0, $<, $@)

%.verify.cvc4: %.pyv prelude
	$(call runmypyvy, verify --exit-0 --cvc4, $<, $@)

%.trace: %.pyv prelude
	$(call runmypyvy, trace, $<, $@)

%.updr: %.pyv prelude
	$(call runmypyvy, updr, $<, $@)

pd-old: prelude
# enumerate-reachable-states
	$(call runmypyvy_grep, \
	enumerate-reachable-states --clear-cache, \
	examples/pd/lockserv.pyv, \
	examples/pd/lockserv.enumerate-reachable-states, \
	"found 25 states")

# forward-explore-inv
	$(call runmypyvy_grep, \
	pd-forward-explore-inv --clear-cache, \
	examples/pd/lockserv_cnf.pyv, \
	examples/pd/lockserv_cnf.forward-explore-inv, \
	-P "  [VX]  ")
#	time $(PYTHON) src/mypyvy.py pd-forward-explore-inv --clear-cache-memo --cache-only-discovered $(MYPYVY_OPTS) examples/pd/lockserv_cnf.pyv > lockserv_cnf_only_discovered.out  # TODO: this currently fails due to not accurately detecting isomorphic states in the cache

# forward-explore-inv with unrolling
	$(call runmypyvy_grep, \
	pd-forward-explore-inv --clear-cache --unroll-to-depth=1, \
	examples/pd/lockserv.pyv, \
	examples/pd/lockserv.forward-explore-inv.1, \
	-P "  [VX]  ")
	$(call runmypyvy_grep, \
	pd-forward-explore-inv --clear-cache --unroll-to-depth=2, \
	examples/pd/lockserv.pyv, \
	examples/pd/lockserv.forward-explore-inv.2, \
	-P "  [VX]  ")
	$(call runmypyvy_grep, \
	pd-forward-explore-inv --clear-cache --unroll-to-depth=3, \
	examples/pd/lockserv.pyv, \
	examples/pd/lockserv.forward-explore-inv.3, \
	-P "  [VX]  ")

	$(call runmypyvy_grep, \
	pd-forward-explore-inv --clear-cache --unroll-to-depth=1, \
	examples/pd/paxos_forall.pyv, \
	examples/pd/paxos_forall.forward-explore-inv.1, \
	-P "  [VX]  ")
	$(call runmypyvy_grep, \
	pd-forward-explore-inv --clear-cache --unroll-to-depth=2, \
	examples/pd/paxos_forall.pyv, \
	examples/pd/paxos_forall.forward-explore-inv.2, \
	-P "  [VX]  ")
#	$(call runmypyvy_grep, \
#	pd-forward-explore-inv --clear-cache --unroll-to-depth=3, \
#	examples/pd/paxos_forall.pyv, \
#	examples/pd/paxos_forall.forward-explore-inv.3, \
#	-P "  [VX]  ")

# repeated-houdini --sharp
	$(call runmypyvy_grep, \
	pd-repeated-houdini --sharp --clear-cache, \
	examples/pd/lockserv.pyv, \
	examples/pd/lockserv.repeated-houdini.sharp, \
	"Implies safety!")
#	time $(PYTHON) src/mypyvy.py pd-repeated-houdini --sharp --cache-only $(MYPYVY_OPTS)   examples/pd/lockserv.pyv > lockserv_cache_only.out # TODO: this is failing, maybe debug it
#	time $(PYTHON) src/mypyvy.py pd-repeated-houdini --sharp --clear-cache-memo --cache-only-discovered $(MYPYVY_OPTS) examples/pd/lockserv.pyv > lockserv_only_discovered.out  # TODO: this currently fails due to not accurately detecting isomorphic states in the cache

# repeated-houdini --no-sharp
	$(call runmypyvy_grep, \
	pd-repeated-houdini --sharp --clear-cache, \
	examples/pd/lockserv.pyv, \
	examples/pd/lockserv.repeated-houdini.no-sharp, \
	"Implies safety!")
#	time $(PYTHON) src/mypyvy.py pd-repeated-houdini --no-sharp --cache-only $(MYPYVY_OPTS)   examples/pd/lockserv.pyv > lockserv_nosharp_cache_only.out # TODO: this is failing, maybe debug it
#	time $(PYTHON) src/mypyvy.py pd-repeated-houdini --no-sharp --clear-cache-memo --cache-only-discovered $(MYPYVY_OPTS) examples/pd/lockserv.pyv > lockserv_nosharp_only_discovered.out # TODO: this currently fails due to not accurately detecting isomorphic states in the cache

# cdcl-invariant
	$(call runmypyvy_grep, \
	pd-cdcl-invariant --clear-cache, \
	examples/pd/lockserv.pyv, \
	examples/pd/lockserv.cdcl-invariant, \
	"Implies safety!")
#	time $(PYTHON) src/mypyvy.py pd-cdcl-invariant --cache-only $(MYPYVY_OPTS) examples/pd/lockserv.pyv > lockserv.cdcl_invariant_cache_only.out

pd: prelude
# primal-dual-houdini

# should take about 1 minute
	$(call runmypyvy_grep, \
	pd-primal-dual-houdini --clear-cache --no-restarts --no-all-subclauses --induction-width=1 --cpus 2, \
	examples/pd/ring.pyv, \
	examples/pd/ring.primal-dual-houdini, \
	"Proved safety!")

# should take about 2 minutes
	$(call runmypyvy_grep, \
	pd-primal-dual-houdini --clear-cache --no-restarts --no-all-subclauses --induction-width=1 --cpus 2, \
	examples/pd/sharded-kv.pyv, \
	examples/pd/sharded-kv.prima-dual-houdini, \
	"Fixed point of induction width reached without a safety proof!")

pd-long: prelude
# primal-dual-houdini for problems that take a long time

# should take about 6 minutes
	$(call runmypyvy_grep, \
	pd-primal-dual-houdini --clear-cache --no-restarts --no-all-subclauses --induction-width=1 --cpus 2, \
	examples/pd/ring-id.pyv, \
	examples/pd/ring-id.primal-dual-houdini, \
	"Proved safety!")

# can take upto 2 hours
	$(call runmypyvy_grep, \
	pd-primal-dual-houdini --clear-cache --no-restarts --no-all-subclauses --induction-width=1 --cpus 2, \
	examples/pd/consensus_forall.pyv, \
	examples/pd/consensus_forall.primal-dual-houdini, \
	"Proved safety!")

# can take a few hours
	$(call runmypyvy_grep, \
	pd-primal-dual-houdini --clear-cache --no-restarts --no-all-subclauses --induction-width=1 --cpus 2, \
	examples/pd/lockserv.pyv, \
	examples/pd/lockserv.primal-dual-houdini, \
	-P "Proved safety\!$$|Fixed point of induction width reached without a safety proof\!$$")

sep: \
	examples/pd/ring.sep \
	examples/pd/ring-id.sep \
	examples/pd/lockserv.sep \
	examples/pd/consensus_forall.sep \

%.sep: %.pyv prelude
	time ( $(PYTHON) src/mypyvy.py sep $(MYPYVY_OPTS) $< > $@.out && \
		echo && head -n 1 $@.out && \
		grep "Successfully learned a total" $@.out )

nightly:
	python3 script/nightly.py

clear-cache:
	rm -iv examples/*.cache examples/*/*.cache

clean:
	rm -fv examples/*.out examples/*/*.out
	rm -fr .mypy_cache/

.PHONY: style check run test verify verify-pd updr bench typecheck trace pd pd-old pd-long unit check-imports clear-cache nightly clean prelude
