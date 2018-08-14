import argparse
import datetime
import random
import re
import statistics
import subprocess

from typing import Optional

class Benchmark(object):
    def __init__(self, name: str, safety: Optional[str]=None) -> None:
        self.name = name
        self.safety = safety

    def __repr__(self) -> str:
        l = []
        l.append(self.name)
        if self.safety is not None:
            l.append('safety=%s' % self.safety)
        return 'Benchmark(%s)' % ','.join(l)

    def run(self, seed: Optional[int]=None) -> datetime.timedelta:
        cmd = ['python3', 'mypyvy.py', 'updr', '--log=info']

        if seed is not None:
            cmd.append('--seed=%s' % seed)

        if self.safety is not None:
            cmd.append('--safety=%s' % self.safety)

        cmd.append('--use-z3-unsat-cores')
        cmd.append(self.name)

        print(' '.join(cmd))
        proc = subprocess.run(cmd, capture_output=True, text=True) # type: ignore

        # print(proc.stderr)
        # print(proc.stdout)

        for line in proc.stderr.splitlines():
            if 'updr ended' in line:
                m = re.search('\(took (?P<dt>.*)\)', line)
                assert m is not None
                dt_string = m.group('dt')
                dt: datetime.timedelta = eval(dt_string)
                return dt

        assert False


benchmarks = [
    Benchmark('lockserv.pyv', safety='mutex'),
    Benchmark('consensus.pyv', safety='one_leader'),
    Benchmark('sharded-kv.pyv', safety='keys_unique')
]

def main() -> None:
    argparser = argparse.ArgumentParser()
    argparser.add_argument('-n', type=int, default=10)
    argparser.add_argument('--random-seeds', action='store_true')

    args = argparser.parse_args()

    if args.random_seeds:
        seeds = [random.randint(0, 2**32-1) for i in range(args.n)]
    else:
        seeds = list(range(args.n))

    data = []
    for b in benchmarks:
        l = []
        for i in range(args.n):
            l.append(b.run(seed=seeds[i]))
        floats = [x.total_seconds() for x in l]
        avg = datetime.timedelta(seconds=statistics.mean(floats))
        stdev = datetime.timedelta(seconds=statistics.stdev(floats))
        data.append((repr(b), str(l), 'avg: %s' % avg, 'stdev: %s' % stdev))

    print('seeds: %s' % seeds)
    for t in data:
        print('\n'.join(t))

if __name__ == '__main__':
    main()
