import ascii_graph
import argparse
import datetime
import numpy
import os
import os.path
import random
import re
import statistics
import subprocess
import sys

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

    def run(self, uid: Optional[int]=None, seed: Optional[int]=None) -> Optional[float]:
        assert args is not None
        cmd = ['python3', 'mypyvy.py', 'updr', '--log=%s' % args.log]

        if seed is not None:
            cmd.append('--seed=%s' % seed)

        if self.safety is not None:
            cmd.append('--safety=%s' % self.safety)

        cmd.extend(args.options)
        cmd.append(self.name)

        print('\r', end='')
        print(' '.join(cmd), end='', flush=True)
        proc = subprocess.run(cmd, capture_output=True, text=True) # type: ignore

        if args.keep_logs:
            assert uid is not None
            name = os.path.basename(self.name)
            name = os.path.splitext(name)[0]
            with open('log-%s-%s' % (name, uid), 'w') as f:
                print(proc.stdout, end='', file=f)

        for line in proc.stdout.splitlines():
            if 'updr ended' in line:
                m = re.search('\(took (?P<time>.*) seconds\)', line)
                assert m is not None
                t = float(m.group('time'))
                return t

        # probably the child job was killed or terminated abnormally
        return None


benchmarks = [
    Benchmark('test/lockserv.pyv', safety='mutex'),
    Benchmark('test/consensus.pyv', safety='one_leader'),
    Benchmark('test/sharded-kv.pyv', safety='keys_unique'),
    Benchmark('test/ring.pyv', safety='safety')
]

def main() -> None:
    argparser = argparse.ArgumentParser()
    argparser.add_argument('-n', type=int, default=10)
    argparser.add_argument('--random-seeds', action='store_true')
    argparser.add_argument('--seeds', nargs='*')
    argparser.add_argument('--list-benchmarks', action='store_true')
    argparser.add_argument('--graph', action='store_true')
    argparser.add_argument('--log', default='info')
    argparser.add_argument('--keep-logs', action='store_true')
    argparser.add_argument('--benchmark', nargs='*', default=[])
    argparser.add_argument('--options', nargs=argparse.REMAINDER, default=[])

    global args
    args = argparser.parse_args()

    if args.list_benchmarks:
        print(' '.join(b.name for b in benchmarks))
        sys.exit(0)


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

    assert not (args.random_seeds and args.seeds is not None)
    if args.random_seeds:
        seeds = [random.randint(0, 2**32-1) for i in range(args.n)]
    elif args.seeds is not None:
        seeds = [int(x) for x in args.seeds]
        args.n = len(seeds)
    else:
        seeds = list(range(args.n))

    data = []
    for b in args.benchmark:
        l = []
        for i in range(args.n):
            l.append(b.run(seed=seeds[i], uid=i))
        print()
        without_timeouts = [x for x in l if x is not None]
        n_timeouts = sum(1 for x in l if x is None)
        avg = statistics.mean(without_timeouts)
        if args.n > 1:
            stdev = statistics.stdev(without_timeouts)
        else:
            stdev = 0.0
        data.append((b, l, avg, stdev, n_timeouts))

    if args.graph:
        g = ascii_graph.Pyasciigraph()

    print('seeds: %s' % seeds)
    for b, l, avg, stdev, n_timeouts in data:
        print('\n'.join([repr(b),
                         str(l),
                         'avg: %s' % avg,
                         'stdev: %s' % stdev,
                         '# timeouts: %s' % n_timeouts
        ]))

        if args.graph:
            without_timeouts = [x for x in l if x is not None]
            h, bins = numpy.histogram(without_timeouts)
            for line in g.graph('title', zip([str(x) for x in bins], [0] + list(h))):
                print(line)



if __name__ == '__main__':
    main()
