import os
import re
import subprocess
from subprocess import CompletedProcess
import multiprocessing as mp
from syntax import *
from logic import *
from typing import TypeVar, Iterable, FrozenSet, Union, Callable, Generator, Set, Optional, cast, Type, Collection, TYPE_CHECKING, AbstractSet

TESTS_ROOT_DIRECTORY_PATH = '/Users/amohamdy/stanford/aiken-1920-research/mypyvy/examples'
KOD_OUTPUT_DIRECTORY = '/Users/amohamdy/stanford/aiken-1920-research/mypyvy/examples/'
MYPYVY_EXECUTABLE_PATH = '/Users/amohamdy/stanford/aiken-1920-research/mypyvy/src/mypyvy.py'

def bench_kod_on(filepath: str) -> None:
    out = None
    print(f'[PID={os.getpid()}] Benchmarking {os.path.basename(filepath)} ... ', end='')
    completed_process: CompletedProcess[str] = subprocess.run(
                    [MYPYVY_EXECUTABLE_PATH, 'kod-benchmark', filepath, KOD_OUTPUT_DIRECTORY],
                    stdout=out,
                    text=True,
                    timeout=1
                )
    print(out)
    print(f'[PID={os.getpid()}] DONE')

def main() -> None:
    # if len(sys.argv) < 2:
    #     print('Usage: python3 benchmark_driver.py [path to root of tests directory] [path to output directory]')
    #     return
    # TESTS_ROOT_DIRECTORY_PATH = sys.argv[1]
    test_files = [os.path.join(root, f) for root, _, files in os.walk(TESTS_ROOT_DIRECTORY_PATH) for f in files if re.match(r'.*[.]pyv', f)]
    # pool = mp.Pool(mp.cpu_count())
    # pool.map(bench_kod_on, test_files)
    # pool.close()
    # print('CALLING MAP')
    for file in test_files:
        bench_kod_on(file)
    # map(bench_kod_on, test_files)

if __name__ == '__main__':
    main()