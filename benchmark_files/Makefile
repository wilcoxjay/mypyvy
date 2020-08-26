SHELL := /bin/bash

KODKOD_JAR_EXECUTABLE_PATH := /scr/padon/kodkod/kodkod.jar:.
KODKOD_LIBRARY_PATH := /scr/padon/kodkod
Z3 := /scr/padon/z3/z3-4.8.8-x64-ubuntu-16.04/bin/z3

KOD_BENCHMARK_FILES := $(sort $(wildcard *.java))

Z3_BENCHMARK_FILES := $(sort $(wildcard *.smt2))

compile: $(patsubst %.java, %.class, $(KOD_BENCHMARK_FILES))

run-kodkod: $(patsubst %.java, %.kodkod.out, $(KOD_BENCHMARK_FILES))

run-z3: $(patsubst %.smt2, %.z3.out, $(Z3_BENCHMARK_FILES))

%.class: %.java
	javac -cp $(KODKOD_JAR_EXECUTABLE_PATH) $<

%.kodkod.out: %.class    

	(/usr/bin/time -f "%e" timeout -v 10m  prlimit --verbose --data=16000000000 java -cp $(KODKOD_JAR_EXECUTABLE_PATH) -Djava.library.path=$(KODKOD_LIBRARY_PATH) $(basename $<) ) &> $@

%.z3.out: %.smt2
	(/usr/bin/time -f "%e" timeout -v 10m  prlimit --verbose --data=16000000000 $(Z3) $< ) &> $@

clean:
	rm -v *.class *.out *.result	

.PHONY: compile run-kodkod run-z3 clean
