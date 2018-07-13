check: mypyvy.py stubs/z3/__init__.pyi
	MYPYPATH=./stubs mypy --py2 mypyvy.py

run: check
	python mypyvy.py

.PHONY: check run
