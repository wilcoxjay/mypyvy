#!/usr/bin/env bash

if type cvc4 &>/dev/null; then
    # if cvc4 is in path
    CVC4CMD=cvc4
else
    # from here on, it is linux specific: we wget cvc4 if needed, or use the one in the current dir
    if type ./cvc4-1.7-x86_64-linux-opt &>/dev/null; then
	CVC4CMD=./cvc4-1.7-x86_64-linux-opt
    else
	wget -q https://github.com/CVC4/CVC4/releases/download/1.7/cvc4-1.7-x86_64-linux-opt &> /dev/null
	chmod +x ./cvc4-1.7-x86_64-linux-opt cvc4
	CVC4CMD=./cvc4-1.7-x86_64-linux-opt
    fi
fi

$CVC4CMD --lang=smtlib2.6 --finite-model-find --full-saturate-quant --produce-models --seed=$RANDOM "$@"
