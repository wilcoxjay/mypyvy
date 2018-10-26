#!/usr/bin/env bash
LOGDIR=logs/$(date '+%y%m%d-%H%M%S')-nightly
time python3 benchmark.py -n 1000 -j 4 --timeout 75 --pin-cores --keep-logs $LOGDIR

pushd $LOGDIR
tar cfz logs.tgz *.log
rm *.log
popd

git add $LOGDIR
