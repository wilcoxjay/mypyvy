check: mypyvy.py stubs/z3/__init__.pyi
	$(eval D := $(shell pwd))
	cd; MYPYPATH=$(D)/stubs mypy --py2 $(D)/mypyvy.py

run: check
	python mypyvy.py

test: check
	time python mypyvy.py lockserv.pyv
	time python mypyvy.py consensus.pyv

.PHONY: check run test
