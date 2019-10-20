#!/usr/bin/env bash

cvc4 --lang=smtlib2.6 --finite-model-find --full-saturate-quant --produce-models "$@"
