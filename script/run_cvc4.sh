#!/usr/bin/env bash

if type cvc4 &>/dev/null; then
    # if cvc4 is in path
    CVC4CMD=cvc4
else
    # from here on, it is linux specific: we wget cvc4 if needed, or use the one in the current dir
    if type ./cvc4-1.8-x86_64-linux-opt &>/dev/null; then
	CVC4CMD=./cvc4-1.8-x86_64-linux-opt
    elif type ./cvc4-1.7-x86_64-linux-opt &>/dev/null; then
	CVC4CMD=./cvc4-1.7-x86_64-linux-opt
    else
	echo "Error: cannot find CVC4 executable" >&2
	exit 1
    fi
fi

$CVC4CMD \
    --lang=smtlib2.6 \
    --finite-model-find \
    --fs-interleave \
    --nl-ext-tplanes \
    --produce-models \
    "$@"
