SHELL := /bin/bash

KODKOD_JAR_EXECUTABLE_PATH := /scr/padon/kodkod/kodkod.jar:.
KODKOD_LIBRARY_PATH := /scr/padon/kodkod

BENCHMARK_FILES := $(sort $(wildcard *.java))

compile: $(patsubst %.java, %.class, $(BENCHMARK_FILES))

run: $(patsubst %.java, %.out, $(BENCHMARK_FILES))

%.class: %.java
	javac -cp'$(KODKOD_JAR_EXECUTABLE_PATH) $<

%.out: %.class    
	(systemd-run --user --scope -p MemoryLimit=10G timeout 10m java -cp $(KODKOD_JAR_EXECUTABLE_PATH) -Djava.library.path=$(KODKOD_LIBRARY_PATH) $< ) &> $@
clean:
	rm -v *.class *.out *.result	

.PHONY: compile run clean
