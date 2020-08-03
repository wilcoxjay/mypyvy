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

runmypyvy = time ( $(PYTHON) src/mypyvy.py $(1) $(MYPYVY_OPTS) $(2) > $(3).out && echo $$'\n'`head -n 1 $(3).out`$$'\n'`tail -n 1 $(3).out` )

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
	time ( $(PYTHON) src/mypyvy.py enumerate-reachable-states --clear-cache $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv.enumerate_reachable_states.out && \
		grep "found 25 states" lockserv.enumerate_reachable_states.out )

# forward-explore-inv
	time $(PYTHON) src/mypyvy.py pd-forward-explore-inv --clear-cache $(MYPYVY_OPTS) examples/lockserv_cnf.pyv > lockserv_cnf_clear_cache.out
#	time $(PYTHON) src/mypyvy.py pd-forward-explore-inv --cache-only $(MYPYVY_OPTS)   examples/lockserv_cnf.pyv > lockserv_cnf_cache_only.out
#	time $(PYTHON) src/mypyvy.py pd-forward-explore-inv --clear-cache-memo --cache-only-discovered $(MYPYVY_OPTS) examples/lockserv_cnf.pyv > lockserv_cnf_only_discovered.out  # TODO: this currently fails due to not accurately detecting isomorphic states in the cache

# forward-explore-inv with unrolling
	time ( $(PYTHON) src/mypyvy.py pd-forward-explore-inv --unroll-to-depth=1 --clear-cache $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv.forward_explore_inv.1.out && \
		grep "  X  " lockserv.forward_explore_inv.1.out )
#	time $(PYTHON) src/mypyvy.py pd-forward-explore-inv --unroll-to-depth=2 --clear-cache $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv.forward_explore_inv.2.out
#	! grep "  X  " lockserv.forward_explore_inv.2.out
#	time $(PYTHON) src/mypyvy.py pd-forward-explore-inv --unroll-to-depth=3 --clear-cache $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv.forward_explore_inv.3.out
#	! grep "  X  " lockserv.forward_explore_inv.3.out
	time ( $(PYTHON) src/mypyvy.py pd-forward-explore-inv --unroll-to-depth=1 --clear-cache $(MYPYVY_OPTS) examples/pd/paxos_forall.pyv > paxos_forall.forward_explore_inv.1.out && \
		grep "  X  " paxos_forall.forward_explore_inv.1.out)
#	time $(PYTHON) src/mypyvy.py pd-forward-explore-inv --unroll-to-depth=2 --clear-cache $(MYPYVY_OPTS) examples/pd/paxos_forall.pyv > paxos_forall.forward_explore_inv.2.out # ~5m
#	grep "  X  " paxos_forall.forward_explore_inv.2.out
#	time $(PYTHON) src/mypyvy.py pd-forward-explore-inv --unroll-to-depth=3 --clear-cache $(MYPYVY_OPTS) examples/pd/paxos_forall.pyv > paxos_forall.forward_explore_inv.3.out # ~5m
#	grep "  X  " paxos_forall.forward_explore_inv.3.out

# repeated-houdini --sharp
	time $(PYTHON) src/mypyvy.py pd-repeated-houdini --sharp --clear-cache $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv_clear_cache.out
#	time $(PYTHON) src/mypyvy.py pd-repeated-houdini --sharp --cache-only $(MYPYVY_OPTS)   examples/lockserv.pyv > lockserv_cache_only.out # TODO: this is failing, maybe debug it
#	time $(PYTHON) src/mypyvy.py pd-repeated-houdini --sharp --clear-cache-memo --cache-only-discovered $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv_only_discovered.out  # TODO: this currently fails due to not accurately detecting isomorphic states in the cache

# repeated-houdini --no-sharp
	time $(PYTHON) src/mypyvy.py pd-repeated-houdini --no-sharp --clear-cache $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv_nosharp_clear_cache.out
#	time $(PYTHON) src/mypyvy.py pd-repeated-houdini --no-sharp --cache-only $(MYPYVY_OPTS)   examples/lockserv.pyv > lockserv_nosharp_cache_only.out # TODO: this is failing, maybe debug it
#	time $(PYTHON) src/mypyvy.py pd-repeated-houdini --no-sharp --clear-cache-memo --cache-only-discovered $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv_nosharp_only_discovered.out # TODO: this currently fails due to not accurately detecting isomorphic states in the cache

# cdcl-invariant
	time $(PYTHON) src/mypyvy.py pd-cdcl-invariant --clear-cache $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv.cdcl_invariant_clear_cache.out
#	time $(PYTHON) src/mypyvy.py pd-cdcl-invariant --cache-only $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv.cdcl_invariant_cache_only.out

pd: prelude
# primal-dual-houdini

# should take about 1 minute
	time ( $(PYTHON) src/mypyvy.py pd-primal-dual-houdini --clear-cache $(MYPYVY_OPTS) --no-restarts --no-all-subclauses --induction-width=1 --cpus 2 examples/pd/ring.pyv > ring.primal_dual_houdini_1_clear_cache.out && \
		grep "Proved safety!" ring.primal_dual_houdini_1_clear_cache.out )

# should take about 2 minutes
	time ( $(PYTHON) src/mypyvy.py pd-primal-dual-houdini --clear-cache $(MYPYVY_OPTS) --no-restarts --no-all-subclauses --induction-width=1 --cpus 2 examples/pd/sharded-kv.pyv > sharded-kv.primal_dual_houdini_1_clear_cache.out && \
		grep "Fixed point of induction width reached without a safety proof!" sharded-kv.primal_dual_houdini_1_clear_cache.out )

pd-long: prelude
# primal-dual-houdini for problems that take a long time

# should take about 6 minutes
	time ( $(PYTHON) src/mypyvy.py pd-primal-dual-houdini --clear-cache $(MYPYVY_OPTS) --no-restarts --no-all-subclauses --induction-width=1 --cpus 2 examples/pd/ring-id.pyv > ring-id.primal_dual_houdini_1_clear_cache.out && \
		grep "Proved safety!" ring-id.primal_dual_houdini_1_clear_cache.out )

# can take upto 2 hours
	time ( $(PYTHON) src/mypyvy.py pd-primal-dual-houdini --clear-cache $(MYPYVY_OPTS) --no-restarts --no-all-subclauses --induction-width=1 --cpus 2 examples/pd/consensus_forall.pyv > consensus_forall.primal_dual_houdini_1_clear_cache.out && \
		grep "Proved safety!" consensus_forall.primal_dual_houdini_1_clear_cache.out )

# can take a few hours
	time ( $(PYTHON) src/mypyvy.py pd-primal-dual-houdini --clear-cache $(MYPYVY_OPTS) --no-restarts --no-all-subclauses --induction-width=1 --cpus 2 examples/pd/lockserv.pyv > lockserv.primal_dual_houdini_1_clear_cache.out && \
		grep -P "Proved safety\!$|Fixed point of induction width reached without a safety proof\!$" lockserv.primal_dual_houdini_1_clear_cache.out )

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
