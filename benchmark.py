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
        cmd = ['python3', 'mypyvy.py', '--log=info']

        if seed is not None:
            cmd.append('--seed=%s' % seed)

        cmd.append('updr')

        if self.safety is not None:
            cmd.append('--safety=%s' % self.safety)

        cmd.append(self.name)

        print(' '.join(cmd))
        proc = subprocess.run(cmd, capture_output=True, text=True) # type: ignore

        # print(proc.stderr)
        # print(proc.stdout)

        for line in proc.stderr.splitlines():
            if 'updr done' in line:
                m = re.search('\((?P<dt>.*) since start\)', line)
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

N = 10

def main() -> None:
    seeds = [random.randint(0, 2**32-1) for i in range(N)]
    data = []
    for b in benchmarks:
        l = []
        for i in range(N):
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
