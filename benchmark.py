import argparse
import datetime
import os
import os.path
import random
import re
import statistics
import subprocess
import sys

from typing import Optional, TextIO

args: argparse.Namespace

class Benchmark(object):
    def __init__(self, name: str, safety: Optional[str]=None) -> None:
        self.name = name
        self.safety = safety

    def __repr__(self) -> str:
        l = []
        l.append(repr(self.name))
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

        cmd.extend(args.args)
        cmd.append(self.name)

        print('\r', end='')
        print(' '.join(cmd), end='', flush=True)
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=args.timeout) # type: ignore
        except subprocess.TimeoutExpired:
            return None

        if args.keep_logs:
            assert uid is not None
            name = os.path.basename(self.name)
            name = os.path.splitext(name)[0]
            if args.log_file_tag is not None:
                tag = '%s-' % args.log_file_tag
            else:
                tag = ''
            if args.experiment is not None:
                dir = args.experiment + os.path.sep
            else:
                dir = ''
            with open('%s%s%s-%s.log' % (dir, tag, name, uid), 'x') as f:
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
    Benchmark('test/lockserv_multi.pyv', safety='mutex'),
    Benchmark('test/consensus.pyv', safety='one_leader'),
    Benchmark('test/sharded-kv.pyv', safety='keys_unique'),
    Benchmark('test/ring.pyv', safety='safety')
]

def main() -> None:
    argparser = argparse.ArgumentParser()
    argparser.add_argument('-n', type=int, default=10,
                           help='number of times to run the benchmark')
    argparser.add_argument('--random-seeds', action='store_true',
                           help='use a randomly generated seed for each run')
    argparser.add_argument('--seeds', nargs='*', metavar='N',
                           help='list of seeds to run')
    argparser.add_argument('--list-benchmarks', action='store_true',
                           help='print known benchmark names and exit')
    argparser.add_argument('--graph', action='store_true',
                           help='show a histogram summarizing the results')
    argparser.add_argument('--log', default='info', choices=['info', 'debug'],
                           help='logging level to pass to mypyvy')
    argparser.add_argument('--log-file-tag',
                           help='additional string to use in log file names')
    argparser.add_argument('--keep-logs', action='store_true',
                           help='save logs to disk')
    argparser.add_argument('--timeout', type=int,
                           help='timeout for each child job')
    argparser.add_argument('experiment', nargs='?',
                           help='directory name to store all logs (if kept) and measurements')
    argparser.add_argument('--benchmark', nargs='*', default=[], metavar='B',
                           help='list of benchmarks to run; default runs all benchmarks')
    argparser.add_argument('--args', nargs=argparse.REMAINDER, default=[],
                           help='additional arguments to pass to mypyvy')

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
                sys.exit(1)
        args.benchmark = bs

    assert not (args.random_seeds and args.seeds is not None)
    if args.random_seeds:
        seeds = [random.randint(0, 2**32-1) for i in range(args.n)]
        print_seeds = True
    elif args.seeds is not None:
        seeds = [int(x) for x in args.seeds]
        args.n = len(seeds)
        print_seeds = True
    else:
        seeds = list(range(args.n))
        print_seeds = False


    if args.experiment is not None:
        os.makedirs(args.experiment, exist_ok=False)
        results_file = open(os.path.join(args.experiment, 'results'), 'x')
    else:
        results_file = sys.stdout

    print(' '.join(['python3'] + sys.argv), file=results_file)

    data = []
    for b in args.benchmark:
        l = []
        for i in range(args.n):
            l.append(b.run(seed=seeds[i], uid=i))
        print()
        without_timeouts = [x for x in l if x is not None]
        n_timeouts = sum(1 for x in l if x is None)
        if len(without_timeouts) > 0:
            avg = statistics.mean(without_timeouts)
        else:
            avg = 0.0
        if len(without_timeouts) > 1:
            stdev = statistics.stdev(without_timeouts)
        else:
            stdev = 0.0
        data.append((b, l, avg, stdev, n_timeouts))

    if args.graph:
        import ascii_graph # type: ignore
        import numpy # type: ignore
        g = ascii_graph.Pyasciigraph()

    if print_seeds:
        print('seeds: %s' % seeds, file=results_file)
    for b, l, avg, stdev, n_timeouts in data:
        lines = [repr(b),
                 str(l),
                 'avg: %s' % avg,
                 'stdev: %s' % stdev,
                 '# timeouts: %s' % n_timeouts
        ]
        print('\n'.join(lines), file=results_file)

        if args.graph:
            without_timeouts = [x for x in l if x is not None]
            h, bins = numpy.histogram(without_timeouts)
            for line in g.graph('title', zip([str(x) for x in bins], [0] + list(h))):
                print(line, file=results_file)



if __name__ == '__main__':
    main()
