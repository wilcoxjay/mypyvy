#!/usr/bin/env bash

for AUTOMATON in '' --automaton '--automaton --sketch'; do
    if [ "$AUTOMATON"x == x ]; then
        TAG="updr"
    else
        TAG=$(echo $AUTOMATON | tr -d '-' | tr ' ' '-' | sed 's/automaton/phase/')
    fi
    LOGDIR=logs/$(date '+%y%m%d-%H%M%S')-$TAG
    echo "$LOGDIR"
    time python3 benchmark.py -n 16 -j 16 --all-benchmarks --timeout 1200 --keep-logs "$LOGDIR" --args $AUTOMATON --simplify-diagram --use-z3-unsat-cores --dont-block-may-cex
done
