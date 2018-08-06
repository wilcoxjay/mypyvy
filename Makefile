check: mypyvy.py stubs/z3/__init__.pyi
	$(eval D := $(shell pwd))
	cd; MYPYPATH=$(D)/stubs mypy --py2 --disallow-untyped-defs $(D)/mypyvy.py

run: check
	python mypyvy.py

test: check lockserv.pyv consensus.pyv sharded-kv.pyv

lockserv.pyv:
	time python mypyvy.py verify lockserv.pyv
	time python mypyvy.py updr --safety=mutex lockserv.pyv

consensus.pyv:
	time python mypyvy.py verify consensus.pyv
	time python mypyvy.py updr --safety=one_leader consensus.pyv

sharded-kv.pyv:
	time python mypyvy.py verify sharded-kv.pyv
	time python mypyvy.py updr --safety=keys_unique sharded-kv.pyv

.PHONY: check run test lockserv.pyv consensus.pyv sharded-kv.pyv
