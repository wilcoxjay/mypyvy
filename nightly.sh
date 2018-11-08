#!/usr/bin/env bash

function cleanup() {
    DIR="$1"

    if [ ! -d "$DIR" ]; then
	echo "not cleaning up non-existant directory $DIR" >&2
	return 1
    fi

    pushd $DIR
    tar cfz logs.tgz *.log
    rm *.log
    popd

    git add $DIR
}


LOGDIR=logs/$(date '+%y%m%d-%H%M%S')-updr
time python3 benchmark.py -n 500 -j 4 --timeout 10 --pin-cores --keep-logs "$LOGDIR"
cleanup "$LOGDIR"

PHASE_ARGS="-n 50 -j 4 --timeout 120 --pin-cores --benchmark test/lockserv.pyv test/lockserv_multi_view.pyv --keep-logs"

for SIMP in '' --simplify-diagram; do
    for MIN in '' --minimize-models; do
	for CORES in '' --use-z3-unsat-core; do
	    TAG='phase'
	    if [ "$SIMP"x != x ]; then
		TAG="${TAG}-simpl"
	    fi
	    if [ "$MIN"x != x ]; then
		TAG="${TAG}-min"
	    fi
	    if [ "$CORES"x != x ]; then
		TAG="${TAG}-cores"
	    fi

	    LOGDIR=logs/$(date '+%y%m%d-%H%M%S')-$TAG
	    time python3 benchmark.py $PHASE_ARGS "$LOGDIR" --args --automaton $SIMP $MIN $CORES
	    cleanup "$LOGDIR"
	done
    done
done
