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


#LOGDIR=logs/$(date '+%y%m%d-%H%M%S')-updr
#time python3 benchmark.py -n 500 -j 16 --timeout 30 --keep-logs "$LOGDIR"
#cleanup "$LOGDIR"

COMMON_ARGS="-n 16 -j 16 --timeout 1200 --benchmark test/sharded-kv-retransmit.pyv --keep-logs"

for AUTOMATON in '' --automaton; do
    for SIMP in '' --simplify-diagram; do
        for MIN in '' --minimize-models; do
            for CORES in '' --use-z3-unsat-core; do
                for MAY in '' --dont-block-may-cex; do
                    if [ "$AUTOMATON"x == x ]; then
			TAG="updr"
		    else
			TAG="phase"
		    fi
                    if [ "$SIMP"x != x ]; then
                       TAG="${TAG}-simpl"
                    fi
                    if [ "$MIN"x != x ]; then
                        TAG="${TAG}-min"
                    fi
                    if [ "$CORES"x != x ]; then
                        TAG="${TAG}-cores"
                    fi
                    if [ "$MAY"x != x ]; then
                        TAG="${TAG}-noblockmay"
                    fi

                    LOGDIR=logs/$(date '+%y%m%d-%H%M%S')-$TAG
		    echo $LOGDIR
                    time python3 benchmark.py $COMMON_ARGS "$LOGDIR" --args $AUTOMATON $SIMP $MIN $CORES $MAY
                    # cleanup "$LOGDIR"
                done
            done
        done
    done
done
