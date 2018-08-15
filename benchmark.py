import argparse
import datetime
import random
import re
import statistics
import subprocess

from typing import Optional

args: Optional[argparse.Namespace] = None

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
        assert args is not None
        cmd = ['python3', 'mypyvy.py', 'updr', '--log=info']

        if seed is not None:
            cmd.append('--seed=%s' % seed)

        if self.safety is not None:
            cmd.append('--safety=%s' % self.safety)

        cmd.extend(args.options)
        cmd.append(self.name)

        print('\r', end='')
        print(' '.join(cmd), end='', flush=True)
        proc = subprocess.run(cmd, capture_output=True, text=True) # type: ignore

        for line in proc.stdout.splitlines():
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
    Benchmark('sharded-kv.pyv', safety='keys_unique'),
    Benchmark('ring.pyv', safety='safety')
]

def main() -> None:
    argparser = argparse.ArgumentParser()
    argparser.add_argument('-n', type=int, default=10)
    argparser.add_argument('--random-seeds', action='store_true')
    argparser.add_argument('--benchmark', nargs='*', default=[])
    argparser.add_argument('--options', nargs=argparse.REMAINDER)

    global args
    args = argparser.parse_args()

    if args.benchmark == []:
        args.benchmark = benchmarks
    else:
        bs = []
        for name in args.benchmark:
            found = False
            for b in benchmarks:
                if b.name == name:
                    bs.append(b)
                    found = True
                    break
            if not found:
                print('unknown benchmark file %s' % name)
        args.benchmark = bs

    if args.random_seeds:
        seeds = [random.randint(0, 2**32-1) for i in range(args.n)]
    else:
        seeds = list(range(args.n))

    data = []
    for b in args.benchmark:
        l = []
        for i in range(args.n):
            l.append(b.run(seed=seeds[i]))
        print()
        floats = [x.total_seconds() for x in l]
        avg = datetime.timedelta(seconds=statistics.mean(floats))
        if args.n > 1:
            stdev = datetime.timedelta(seconds=statistics.stdev(floats))
        else:
            stdev = datetime.timedelta(seconds=0)
        data.append((repr(b), str(l), 'avg: %s' % avg, 'stdev: %s' % stdev))

    print('seeds: %s' % seeds)
    for t in data:
        print('\n'.join(t))

if __name__ == '__main__':
    main()
