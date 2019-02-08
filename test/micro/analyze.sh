#!/usr/bin/env bash

set -e
set -x

LOGDIR=$1

pushd $LOGDIR

function go() {
    PATTERN=$1
    wc -l *.$PATTERN
    egrep -Hni 'updr ended' *.$PATTERN | sed -e 's/^log\.\([0-9]*\)[^ ]*INFO/\1 INFO/' -e 's/INFO.*took //'  -e 's/ seconds)//' | sort -n | \
        awk '{printf "%s,%s\n", $1, $2}' > $PATTERN.csv
}

go updr

go automaton_short

go automaton_long

popd

python3 plot.py $LOGDIR > $LOGDIR/plot.tex

pushd $LOGDIR
  pdflatex plot >/dev/null 2>&1
popd

