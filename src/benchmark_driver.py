import os
import re
import subprocess
import multiprocessing as mp
from syntax import *
from logic import *
from typing import TypeVar, Iterable, FrozenSet, Union, Callable, Generator, Set, Optional, cast, Type, Collection, TYPE_CHECKING, AbstractSet

TESTS_ROOT_DIRECTORY_PATH = '/Users/amohamdy/stanford/aiken-1920-research/mypyvy/examples'
MYPYVY_EXECUTABLE_PATH = '/Users/amohamdy/stanford/aiken-1920-research/mypyvy/src/mypyvy.py'

def bench_kod_on(filepath: str):
    out: str = subprocess.check_output(
                    [MYPYVY_EXECUTABLE_PATH, 'kod-benchmark', filepath],
                    text=True,
                ) #TODO timeout=??
    print(f'[PID={os.getpid()}] Benchmarking {os.path.basename(filepath)} ...')
    print(out)
    print(f'[PID={os.getpid()}] DONE')

def main():
    test_files = [os.path.join(root, f) for root, _, files in os.walk(TESTS_ROOT_DIRECTORY_PATH) for f in files if re.match('.*\.pyv', f)]
    pool = mp.Pool(mp.cpu_count())
    pool.map(bench_kod_on, test_files)
    pool.close()

if __name__ == '__main__':
    main()