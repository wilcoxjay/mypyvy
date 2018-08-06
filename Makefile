check: mypyvy.py stubs/z3/__init__.pyi
	$(eval D := $(shell pwd))
	cd; MYPYPATH=$(D)/stubs mypy --py2 --disallow-untyped-defs $(D)/mypyvy.py

test: check unittest verify updr

unittest: unittest.py
	python unittest.py

verify: check lockserv.verify consensus.verify sharded-kv.verify

updr: lockserv.updr consensus.updr sharded-kv.updr

%.verify: %.pyv
	time python mypyvy.py verify $<

lockserv.updr:
	time python mypyvy.py updr --safety=mutex lockserv.pyv

consensus.updr:
	time python mypyvy.py updr --safety=one_leader consensus.pyv

sharded-kv.updr:
	time python mypyvy.py updr --safety=keys_unique sharded-kv.pyv

.PHONY: check run unittest test verify updr lockserv.updr consensus.updr sharded-kv.updr
