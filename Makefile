check: mypyvy.py stubs/z3/__init__.pyi
	$(eval D := $(shell pwd))
	cd; MYPYPATH=$(D)/stubs mypy --py2 $(D)/mypyvy.py

run: check
	python mypyvy.py

.PHONY: check run
