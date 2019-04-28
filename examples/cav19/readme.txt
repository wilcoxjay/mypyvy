This directory contains the mypyvy files for the examples in the CAV'17 paper, Section 6.2. 
The correspondence between this directory and the examples in the paper is as follows (by order of appearance in Table 1):

1. Lock service (single lock) --> lockserv.pyv
2. Lock service (multiple locks) --> lockserv_multi.pyv
3. Consensus --> consensus.pyv
4. KV (basic) [sharded key-value store (without retransmissions)] --> sharded-kv.pyv
5. Ring leader --> ring.pyv
6. KV-R [sharded key-value store with retransmissions] --> sharded-kv-retransmit.pyv
7. Cache coherence --> cache_one.pyv

The examples discussed in the section "Anatomy of the Benefit of Phases" are as follows:

8. Phase decomposition --> see Ring leader above
9. Disabled transitions --> lockserv_multi_no_disabled.pyv
10. Explicit phases --> sharded-kv-retransmit-ghost-view-disabled.pyv