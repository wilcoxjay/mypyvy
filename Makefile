PYTHON := python3.8 -u
MYPYVY_OPTS := --seed=0 --log=warning --timeout 60000

SRC_FILES := $(shell find src -name '*.py' -not -name '*parsetab*' -not -path '*/ply/*')

style:
	$(PYTHON) -m flake8 $(SRC_FILES) || true
	grep the_program $(SRC_FILES) || true

check:
	$(PYTHON) -m mypy --config-file ./mypy.ini $(SRC_FILES)

test: check check-imports unit typecheck verify verify-pd trace updr pd-old pd sep

unit: check
	$(PYTHON) -m unittest discover -s src -v

typecheck: $(patsubst %.pyv, %.typecheck, $(wildcard examples/*.pyv examples/*/*.pyv))

verify: examples/lockserv.verify examples/consensus.verify examples/sharded-kv.verify examples/pd/paxos_epr.verify examples/pd/paxos_forall.verify

verify-pd: \
	examples/pd/cache.verify \
	examples/pd/consensus_epr.verify \
	examples/pd/consensus_forall.verify \
	examples/pd/lockserv.verify \
	examples/pd/paxos_epr.verify \
	examples/pd/paxos_forall.verify \
	examples/pd/paxos_forall_choosable.verify \
	examples/pd/ring-id.verify \
	examples/pd/ring.verify \
	examples/pd/sharded-kv-retransmit.verify \
	examples/pd/sharded-kv.verify \
	examples/pd/stoppable_paxos_epr.verify \
	examples/pd/stoppable_paxos_forall.verify \
	examples/pd/stoppable_paxos_forall_choosable.verify \
	examples/pd/tlb_safety.verify \

trace: $(patsubst %.pyv, %.trace, $(wildcard examples/*.pyv))

updr: examples/lockserv.updr examples/sharded-kv.updr

%.typecheck: %.pyv
	$(PYTHON) src/mypyvy.py typecheck $(MYPYVY_OPTS) $<

%.trace: %.pyv
	$(PYTHON) src/mypyvy.py trace $(MYPYVY_OPTS) $<

%.verify: %.pyv
	time $(PYTHON) src/mypyvy.py verify $(MYPYVY_OPTS) $<

%.updr: %.pyv
	time $(PYTHON) src/mypyvy.py updr $(MYPYVY_OPTS) $<

pd-old:
	# enumerate-reachable-states
	time $(PYTHON) src/mypyvy.py enumerate-reachable-states $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv.enumerate_reachable_states.log
	grep "found 25 states" lockserv.enumerate_reachable_states.log

	# forward-explore-inv
	time $(PYTHON) src/mypyvy.py pd-forward-explore-inv --clear-cache $(MYPYVY_OPTS) examples/lockserv_cnf.pyv > lockserv_cnf_clear_cache.log
	time $(PYTHON) src/mypyvy.py pd-forward-explore-inv --cache-only $(MYPYVY_OPTS)   examples/lockserv_cnf.pyv > lockserv_cnf_cache_only.log
	# time $(PYTHON) src/mypyvy.py pd-forward-explore-inv --clear-cache-memo --cache-only-discovered $(MYPYVY_OPTS) examples/lockserv_cnf.pyv > lockserv_cnf_only_discovered.log  # TODO: this currently fails due to not accurately detecting isomorphic states in the cache

	# forward-explore-inv with unrolling
	time $(PYTHON) src/mypyvy.py pd-forward-explore-inv --unroll-to-depth=1 $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv.forward_explore_inv.1.log
	grep "  X  " lockserv.forward_explore_inv.1.log
# 	time $(PYTHON) src/mypyvy.py pd-forward-explore-inv --unroll-to-depth=2 $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv.forward_explore_inv.2.log
# 	! grep "  X  " lockserv.forward_explore_inv.2.log
# 	time $(PYTHON) src/mypyvy.py pd-forward-explore-inv --unroll-to-depth=3 $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv.forward_explore_inv.3.log
# 	! grep "  X  " lockserv.forward_explore_inv.3.log
	time $(PYTHON) src/mypyvy.py pd-forward-explore-inv --unroll-to-depth=1 $(MYPYVY_OPTS) examples/pd/paxos_forall.pyv > paxos_forall.forward_explore_inv.1.log
	grep "  X  " paxos_forall.forward_explore_inv.1.log
#	time $(PYTHON) src/mypyvy.py pd-forward-explore-inv --unroll-to-depth=2 $(MYPYVY_OPTS) examples/pd/paxos_forall.pyv > paxos_forall.forward_explore_inv.2.log # ~5m
# 	grep "  X  " paxos_forall.forward_explore_inv.2.log
# 	time $(PYTHON) src/mypyvy.py pd-forward-explore-inv --unroll-to-depth=3 $(MYPYVY_OPTS) examples/pd/paxos_forall.pyv > paxos_forall.forward_explore_inv.3.log # ~5m
# 	grep "  X  " paxos_forall.forward_explore_inv.3.log

	# repeated-houdini --sharp
	time $(PYTHON) src/mypyvy.py pd-repeated-houdini --sharp --clear-cache $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv_clear_cache.log
	# time $(PYTHON) src/mypyvy.py pd-repeated-houdini --sharp --cache-only $(MYPYVY_OPTS)   examples/lockserv.pyv > lockserv_cache_only.log # TODO: this is failing, maybe debug it
	# time $(PYTHON) src/mypyvy.py pd-repeated-houdini --sharp --clear-cache-memo --cache-only-discovered $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv_only_discovered.log  # TODO: this currently fails due to not accurately detecting isomorphic states in the cache

	# repeated-houdini --no-sharp
	time $(PYTHON) src/mypyvy.py pd-repeated-houdini --no-sharp --clear-cache $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv_nosharp_clear_cache.log
	# time $(PYTHON) src/mypyvy.py pd-repeated-houdini --no-sharp --cache-only $(MYPYVY_OPTS)   examples/lockserv.pyv > lockserv_nosharp_cache_only.log # TODO: this is failing, maybe debug it
	# time $(PYTHON) src/mypyvy.py pd-repeated-houdini --no-sharp --clear-cache-memo --cache-only-discovered $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv_nosharp_only_discovered.log # TODO: this currently fails due to not accurately detecting isomorphic states in the cache

	# cdcl-invariant
	time $(PYTHON) src/mypyvy.py pd-cdcl-invariant --clear-cache $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv.cdcl_invariant_clear_cache.log
	time $(PYTHON) src/mypyvy.py pd-cdcl-invariant --cache-only $(MYPYVY_OPTS) examples/lockserv.pyv > lockserv.cdcl_invariant_cache_only.log

pd:
	# primal-dual-houdini

	# should take about 1 minute
	time $(PYTHON) src/mypyvy.py pd-primal-dual-houdini --clear-cache $(MYPYVY_OPTS) --no-restarts --no-all-subclauses --induction-width=1 --cpus 2 examples/pd/ring.pyv > ring.primal_dual_houdini_1_clear_cache.log
	grep "Proved safety!" ring.primal_dual_houdini_1_clear_cache.log

	# should take about 2 minutes
	time $(PYTHON) src/mypyvy.py pd-primal-dual-houdini --clear-cache $(MYPYVY_OPTS) --no-restarts --no-all-subclauses --induction-width=1 --cpus 2 examples/pd/sharded-kv.pyv > sharded-kv.primal_dual_houdini_1_clear_cache.log
	grep "Fixed point of induction width reached without a safety proof!" sharded-kv.primal_dual_houdini_1_clear_cache.log

pd-long:
	# primal-dual-houdini for problems that take a long time

	# should take about 6 minutes
	time $(PYTHON) src/mypyvy.py pd-primal-dual-houdini --clear-cache $(MYPYVY_OPTS) --no-restarts --no-all-subclauses --induction-width=1 --cpus 2 examples/pd/ring-id.pyv > ring-id.primal_dual_houdini_1_clear_cache.log
	grep "Proved safety!" ring-id.primal_dual_houdini_1_clear_cache.log

	# can take upto 2 hours
	time $(PYTHON) src/mypyvy.py pd-primal-dual-houdini --clear-cache $(MYPYVY_OPTS) --no-restarts --no-all-subclauses --induction-width=1 --cpus 2 examples/pd/consensus_forall.pyv > consensus_forall.primal_dual_houdini_1_clear_cache.log
	grep "Proved safety!" consensus_forall.primal_dual_houdini_1_clear_cache.log

	# can take a few hours
	time $(PYTHON) src/mypyvy.py pd-primal-dual-houdini --clear-cache $(MYPYVY_OPTS) --no-restarts --no-all-subclauses --induction-width=1 --cpus 2 examples/pd/lockserv.pyv > lockserv.primal_dual_houdini_1_clear_cache.log
	grep -P "Proved safety\!$|Fixed point of induction width reached without a safety proof\!$" lockserv.primal_dual_houdini_1_clear_cache.log

sep:
	time $(PYTHON) src/mypyvy.py sep examples/pd/ring.pyv > ring.sep.log
	grep "Successfully learned a total" ring.sep.log
	time $(PYTHON) src/mypyvy.py sep examples/pd/ring-id.pyv > ring-id.sep.log
	grep "Successfully learned a total" ring-id.sep.log
	time $(PYTHON) src/mypyvy.py sep examples/pd/lockserv.pyv > lockserv.sep.log
	grep "Successfully learned a total" lockserv.sep.log
	time $(PYTHON) src/mypyvy.py sep examples/pd/consensus_forall.pyv > consensus_forall.sep.log
	grep "Successfully learned a total" consensus_forall.sep.log

check-imports: $(patsubst %.py, %.importable, $(SRC_FILES))

src/%.importable: src/%.py
	@cd src; $(PYTHON) -c "import $(shell basename -s .py $<)" || { echo "file $< is not importable"; exit 1; }

nightly:
	python3 script/nightly.py

clear-cache:
	rm -iv examples/*.cache examples/*/*.cache

.PHONY: style check run test verify verify-pd updr bench typecheck trace pd pd-old pd-long unit check-imports clear-cache nightly
