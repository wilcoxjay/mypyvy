import os
import re
import subprocess
from subprocess import CompletedProcess
import multiprocessing as mp
from typing import TypeVar, Iterable, FrozenSet, Union, Callable, Generator, Set, Optional, cast, Type, Collection, TYPE_CHECKING, AbstractSet

TESTS_ROOT_DIRECTORY_PATH = '/Users/amohamdy/stanford/aiken-1920-research/mypyvy/examples'
MYPYVY_EXECUTABLE_PATH = '/Users/amohamdy/stanford/aiken-1920-research/mypyvy/src/mypyvy.py'

already_checked = [
                    'lockserv_multi.pyv',
                    'paxos_fol.pyv',
                    'sharded-kv-retransmit.pyv',
                    'consensus.pyv',
                  ]

errored_files = [
                    'cache_one.pyv',
                    'crawler.pyv',
                    'crawler-cti.pyv',
                    'parity.pyv',
                    'indigo_tournament.pyv',
                    'nopath.pyv',
                    'raft.pyv',
                    'cache_unsafe.pyv',
                    'consensus_unsafe.pyv',
                    'consensus_unsafe2.pyv',
                    'lockserv_unsafe.pyv',
                    'paxos_forall_choosable_unsafe.pyv',
                    'paxos_forall_choosable_unsafe2.pyv',
                    'paxos_forall_choosable_unsafe_no_intersection.pyv',
                    'sharded-kv-retransmit_unsafe.pyv',
                    'sharded-kv_unsafe.pyv',
                    'sharded-kv_unsafe2.pyv',
                ]

def bench_kod_on(filepath: str) -> None:
    print(f'[PID={os.getpid()}] Benchmarking {os.path.basename(filepath)} ... ', end='')
    try:
        subprocess.run(
            [MYPYVY_EXECUTABLE_PATH, 'kod-benchmark', filepath],
            timeout=60*60
        )
    except subprocess.TimeoutExpired:
        print(f'{os.path.basename(filepath)}: TIMED OUT!')
    print(f'[PID={os.getpid()}] DONE')

def bench_z3_on(filepath: str) -> None:
    print(f'[PID={os.getpid()}] Benchmarking {os.path.basename(filepath)} ... ', end='')
    try:
        subprocess.run(
            [MYPYVY_EXECUTABLE_PATH, 'z3-benchmark', filepath],
            timeout=60*60
        )
    except subprocess.TimeoutExpired:
        print(f'{os.path.basename(filepath)}: TIMED OUT!')
    print(f'[PID={os.getpid()}] DONE')

def main() -> None:
    if len(sys.argv > 1) and sys.argv[1] == 'z3':
        bench = bench_z3_on
    else:
        bench = bench_kod_on
    test_files = [os.path.join(root, f) for root, _, files in os.walk(TESTS_ROOT_DIRECTORY_PATH) for f in files if re.match(r'.*[.]pyv', f)]
    for file in test_files:
        if os.path.basename(file) in already_checked or os.path.basename(file) in errored_files:
            print(f'Already Checked: {os.path.basename(file)}')
        else:
            bench(file)

if __name__ == '__main__':
    main()