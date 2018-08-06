check: mypyvy.py stubs/z3/__init__.pyi
	$(eval D := $(shell pwd))
	cd; MYPYPATH=$(D)/stubs mypy --py2 $(D)/mypyvy.py

run: check
	python mypyvy.py

test: check
	time python mypyvy.py verify lockserv.pyv
	time python mypyvy.py updr --safety=mutex lockserv.pyv
	time python mypyvy.py verify consensus.pyv
	time python mypyvy.py updr --safety=one_leader consensus.pyv

.PHONY: check run test
