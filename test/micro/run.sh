#!/usr/bin/env bash

set -e
set -x


N=10

TIMESTAMP=$(date '+%Y%m%d-%H%M%S')
LOGDIR="logs-$(hostname)-${TIMESTAMP}"
LOG=$LOGDIR/log

mkdir -p $LOGDIR

exec 3>&1 1>$LOG 2>&1

tail -f $LOG >&3 &
TAIL_PID=$!
disown $TAIL_PID

cp micro.py $LOGDIR

pushd $LOGDIR

OPTIONS="--log=info --simplify-diagram --use-z3-unsat-cores --dont-block-may-cex"

for (( i = 2 ; i <= $N ; i++ )) ; do

    echo $i

    python3 micro.py --mode=short $i

    time mypyvy updr $OPTIONS micro.$i.pvy \
           > log.$i.updr 2>&1

    
    time mypyvy updr $OPTIONS --automaton micro.$i.pvy \
           > log.$i.automaton_short 2>&1

    python3 micro.py --mode=long $i

    time mypyvy updr $OPTIONS --automaton micro.$i.pvy \
           > log.$i.automaton_long 2>&1
done

popd

./analyze.sh $LOGDIR

kill -9 $TAIL_PID
