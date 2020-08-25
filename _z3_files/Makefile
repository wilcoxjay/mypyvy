SHELL := /bin/bash

Z3 := /Users/amohamdy/stanford/aiken-1920-research/z3/build/z3

BENCHMARK_FILES := $(sort $(wildcard *.smt2))

run: $(patsubst %.smt2, %.z3.out, $(BENCHMARK_FILES))

%.z3.out: %.smt2    
	(/usr/bin/time $(Z3) $< ) &> $@

clean:
	rm -v *.z3.out

.PHONY: run clean
