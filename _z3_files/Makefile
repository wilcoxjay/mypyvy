SHELL := /bin/bash

Z3 := /scr/padon/z3/z3-4.8.8-x64-ubuntu-16.04/bin/z3

BENCHMARK_FILES := $(sort $(wildcard *.smt2))

run: $(patsubst %.smt2, %.z3.out, $(BENCHMARK_FILES))

%.z3.out: %.smt2    
	(systemd-run --user --scope -p MemoryLimit=10G timeout -v 10m /usr/bin/time -f "%e" $(Z3) $< ) &> $@

clean:
	rm -v *.z3.out

.PHONY: run clean
