#!/usr/bin/env bash


LOGDIR=logs/$(date '+%y%m%d-%H%M%S')-updr-skv-ghost
echo "$LOGDIR"
time python3 benchmark.py -n 16 -j 16 --benchmark examples/sharded-kv-retransmit-ghost-view-disabled.pyv  --timeout 3600 --keep-logs "$LOGDIR" --args --simplify-diagram --use-z3-unsat-cores --dont-block-may-cex


# for AUTOMATON in '' --automaton '--automaton --sketch'; do
#     if [ "$AUTOMATON"x == x ]; then
#         TAG="updr"
#     else
#         TAG=$(echo $AUTOMATON | tr -d '-' | tr ' ' '-' | sed 's/automaton/phase/')
#     fi
#     LOGDIR=logs/$(date '+%y%m%d-%H%M%S')-cache-one-$TAG
#     echo "$LOGDIR"
#     time python3 benchmark.py -n 16 -j 16 --all-benchmarks --timeout 1200 --keep-logs "$LOGDIR" --args $AUTOMATON --simplify-diagram --use-z3-unsat-cores --dont-block-may-cex
# done
