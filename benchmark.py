import argparse
import os
import os.path
import queue
import random
import re
import statistics
import subprocess
import sys
import threading

from typing import Optional, TextIO, List, Tuple, Union

args: argparse.Namespace

def generate_parser() -> None:
    cmd = ['python3.7', 'mypyvy.py', 'generate-parser', 'test/lockserv.pyv']
    subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL) # type: ignore

def run_isolated_process(cmd: List[str], out: TextIO) -> None:
    proc = subprocess.run(cmd, stdin=subprocess.DEVNULL, capture_output=True, text=True) # type: ignore
    print(proc.stdout, end='', file=out)
    print(proc.stderr, end='', file=out)

def dump_version_info(f: TextIO) -> None:
    if f.isatty():
        return
    print('dump_version_info: dumping information about the current commit and working directory', file=f)
    run_isolated_process(['git', 'rev-parse', 'HEAD'], f)
    run_isolated_process(['git', 'status'], f)
    run_isolated_process(['git', 'diff'], f)
    run_isolated_process(['git', 'diff', '--cached'], f)
    print('dump_version_info: done.', file=f)
    print('-' * 80, file=f)

class Benchmark(object):
    def __init__(self, name: str) -> None:
        self.name = name

    def __repr__(self) -> str:
        l = []
        l.append(repr(self.name))
        return 'Benchmark(%s)' % ','.join(l)

    def run(self, uid: Optional[int]=None, seed: Optional[int]=None, worker_id: Optional[int]=None) -> Optional[Tuple[float, int]]:
        assert args is not None
        cmd = ['python3.7', 'mypyvy.py', 'updr', '--forbid-parser-rebuild', '--log=%s' % args.log]

        if args.pin_cores and worker_id is not None:
            cmd = ['taskset', hex(1 << worker_id), ] + cmd

        if seed is not None:
            cmd.append('--seed=%s' % seed)

        cmd.extend(args.args)
        cmd.append(self.name)

        timed_out = False
        timed_out_stdout = None
        timed_out_stderr = None
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=args.timeout) # type: ignore
        except subprocess.TimeoutExpired as e:
            # print('timeout uid %s' % uid)
            timed_out = True
            timed_out_stdout = e.stdout
            timed_out_stderr = e.stderr

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
                if not timed_out:
                    print(proc.stdout, end='', file=f)
                else:
                    print(timed_out_stdout, end='', file=f)

        if not timed_out:
            nqueries: Optional[int] = None
            found = False
            for line in proc.stdout.splitlines():
                if 'updr ended' in line:
                    m = re.search('\(took (?P<time>.*) seconds\)', line)
                    assert m is not None
                    time = float(m.group('time'))
                    found = True
                if 'total number of queries' in line:
                    m = re.search('total number of queries: (?P<nqueries>.*)', line)
                    assert m is not None
                    nqueries = int(m.group('nqueries'))

            if found:
                assert nqueries is not None
                return time, nqueries

        # probably the child job was killed or terminated abnormally
#        print('could not find "updr ended" in job %s' % uid)
#        print('timed_out = %s' % timed_out)
#        if not timed_out:
#            print(proc.stdout)
#            print(proc.stderr)
#        else:
#            print(timed_out_stdout)
#            print(timed_out_stderr)

        return None


convergant_benchmarks = [
    Benchmark('test/lockserv.pyv'),
    Benchmark('test/lockserv_multi.pyv'),
    Benchmark('test/consensus.pyv'),
    Benchmark('test/consensus-0.1.pyv'),
    Benchmark('test/sharded-kv.pyv'),
    Benchmark('test/sharded-kv-retransmit.pyv'),
    Benchmark('test/ring.pyv'),
    Benchmark('test/sll-reverse.pyv'),
]

other_benchmarks: List[Benchmark] = [
    Benchmark('test/cache.pyv'),
    Benchmark('test/paxos.pyv'),
]

all_benchmarks = convergant_benchmarks + other_benchmarks

seeds: List[int] = []

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
    argparser.add_argument('--all-benchmarks', action='store_true',
                           help='run all benchmarks, even potentially nonconvergent ones')
    argparser.add_argument('--benchmark', nargs='*', default=[], metavar='B',
                           help='list of benchmarks to run; default runs all convergent benchmarks')
    argparser.add_argument('-j', '--threads', type=int, metavar='N', default=1,
                           help='number of threads to use')
    argparser.add_argument('--pin-cores', action='store_true',
                           help='use taskset command to set processor affinity of each run')
    argparser.add_argument('--args', nargs=argparse.REMAINDER, default=[],
                           help='additional arguments to pass to mypyvy')

    global args
    args = argparser.parse_args()

    if args.list_benchmarks:
        print(' '.join(b.name for b in all_benchmarks))
        sys.exit(0)

    if args.benchmark != [] and args.all_benchmarks:
        print('cannot pass both --all-benchmarks and --benchmark')
        sys.exit(1)

    if args.benchmark == []:
        if not args.all_benchmarks:
            args.benchmark = convergant_benchmarks
        else:
            args.benchmark = all_benchmarks
    else:
        bs = []
        for name in args.benchmark:
            found = False
            for b in all_benchmarks:
                if b.name == name:
                    bs.append(b)
                    found = True
                    break
            if not found:
                if os.path.exists(name):
                    bs.append(Benchmark(name))
                else:
                    print('unknown benchmark file %s' % name)
                    sys.exit(1)
        args.benchmark = bs

    global seeds
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

    print(' '.join(['python3.7'] + sys.argv), file=results_file)

    dump_version_info(results_file)

    generate_parser()

    q: queue.Queue[Optional[Tuple[Benchmark, int]]] = queue.Queue()
    threads: List[threading.Thread] = []
    results: List[List[Tuple[int, Optional[Tuple[float,int]]]]] = []
    cv = threading.Condition()

    work_done = threading.Event()
    the_bench: Benchmark

    def ui_worker() -> None:
        # print('ui worker starting')
        while True:
            with cv:
                cv.wait()

            if work_done.is_set():
                break

            n = q.unfinished_tasks # type: ignore
            if sys.stdout.isatty():
                print('\r', end='')
                print('benchmark %s has %s jobs remaining' % (the_bench.name, n), end='', flush=True)

        # print('ui worker exiting')

    def worker(id: int) -> None:
        # print('worker %d starting' % id)
        while True:
            item = q.get()
            if item is None:
                break
            (b, i) = item
            try:
                ans = b.run(seed=seeds[i], uid=i, worker_id=id)
            except Exception as e:
                print('worker %s observed exception %s' % (id, repr(e)))
                break
            results[id].append((i, ans))
            q.task_done()
            with cv:
                cv.notify()
        # print('worker %d exiting' % id)

    for tid in range(args.threads):
        t = threading.Thread(target=worker, args=(tid,))
        t.start()
        threads.append(t)

    ui_thread = threading.Thread(target=ui_worker)
    ui_thread.start()

    data = []
    for b in args.benchmark:
        the_bench = b
        results = [[] for _ in threads]
        l = []
        for i in range(args.n):
            q.put((b, i))
        with cv:
            cv.notify()
        q.join()
        print()

        for lr in results:
            l.extend(lr)

        l.sort(key=lambda p: p[0])
        times = [p[1] for p in l]

        without_timeouts = [x for x in times if x is not None]
        n_timeouts = sum(1 for x in times if x is None)

        def safe_summary_stats(l: List[Union[float,int]]) -> Tuple[float, float]:
            if len(l) > 0:
                avg = statistics.mean(l)
            else:
                avg = 0.0
            if len(l) > 1:
                stdev = statistics.stdev(l)
            else:
                stdev = 0.0

            return avg, stdev

        avg_time, stdev_time = safe_summary_stats([t[0] for t in without_timeouts])
        avg_queries, stdev_queries = safe_summary_stats([t[1] for t in without_timeouts])

        data.append((b, times, avg_time, stdev_time, avg_queries, stdev_queries, n_timeouts))

    print()

    if args.graph:
        import ascii_graph # type: ignore
        import numpy # type: ignore
        g = ascii_graph.Pyasciigraph()

    if print_seeds:
        print('seeds: %s' % seeds, file=results_file)
    for b, times, avg_time, stdev_time, avg_queries, stdev_queries, n_timeouts in data:
        lines = [repr(b),
                 str(times),
                 'avg_time: %s' % avg_time,
                 'stdev_time: %s' % stdev_time,
                 'avg_nqueries: %s' % avg_queries,
                 'stdev_nqueries: %s' % stdev_queries,
                 '# timeouts: %s' % n_timeouts
        ]
        print('\n'.join(lines), file=results_file)

        if args.graph:
            without_timeouts = [x for x in times if x is not None]
            h, bins = numpy.histogram(without_timeouts)
            for line in g.graph('title', zip([str(x) for x in bins], [0] + list(h))):
                print(line, file=results_file)

    for _ in threads:
        q.put(None)

    work_done.set()

    while ui_thread.is_alive():
        with cv:
            cv.notify()
        ui_thread.join(timeout=1)

    for t in threads:
        t.join()


if __name__ == '__main__':
    main()
