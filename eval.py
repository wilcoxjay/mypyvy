from __future__ import annotations
import argparse
import matplotlib.pyplot as plt  # type: ignore
import math
import numpy as np  # type: ignore
import pdb
import sys
from typing import List, Optional, Tuple, TextIO, Union, Sequence, Any, Callable

def get_all_matching_data(buf: TextIO, pattern: str, exclude: Optional[str]) -> Sequence[Tuple[str, Sequence[Optional[Union[float, Tuple[float, int]]]]]]:
    matched = False
    benchmark_name = ''
    data = []
    for line in buf:
        if matched:
            data.append((benchmark_name, eval(line)))
            matched = False
        if pattern in line and (exclude is None or exclude not in line):
            matched = True
            tail = line[len("Benchmark('"):]
            benchmark_name = tail[:tail.index("'")]

    return data



def index(axs: Any, nrows: int, ncols: int, i: int, j: int) -> Any:
    if nrows == 1:
        assert i == 0
        if ncols == 1:
            assert j == 0
            return axs
        else:
            return axs[j]
    else:
        if ncols == 1:
            assert j == 0
            return axs[i]
        else:
            return axs[i][j]


def hist(all_data: Sequence[Tuple[str, Sequence[Tuple[str, Sequence[Optional[Union[float,int]]]]]]]) -> None:
    length = len(all_data[0][1])
    assert all(len(l) == length for _, l in all_data)
    ncols = math.ceil(math.sqrt(length))
    nrows = math.ceil(length / ncols)

    fig, axs = plt.subplots(nrows, ncols)

    fig.subplots_adjust(hspace=.6, wspace=.4)

    dims = [(i, j) for i in range(nrows) for j in range(ncols)]

    labels = [t for t, _ in all_data]
    hists = []

    timeout_distance = 2

    for k in range(length):
        tdata = []
        lo = np.PINF
        hi = np.NINF
        any_timeouts = False
        all_timeouts = True
        for nm, run in all_data:
            _, data = run[k]
            lo = min(lo, min((x for x in data if x is not None), default=lo))
            hi = max(hi, max((x for x in data if x is not None), default=hi))
            any_timeouts |= any(x is None for x in data)
            all_timeouts &= all(x is None for x in data)

        if all_timeouts:
            continue

        for nm, run in all_data:
            _, data = run[k]
            tdata.append([(x if x is not None else timeout_distance * hi) for x in data])
        i, j = dims[k]

        a = index(axs, nrows, ncols, i, j)
        _, _, patches = a.hist(tdata, bins=15, label=labels, range=(0, max(max(run) for run in tdata)))
        hists.append(patches)
        title = all_data[0][1][k][0]
        a.set_title(title)
        a.set_xlabel(args.column)
        a.set_ylabel('frequency')

        if any_timeouts:
            a.axvline(x=math.sqrt(timeout_distance) * hi, color='black')

    fig.legend(hists[0], labels)
    plt.show()

def violin(all_data: Sequence[Tuple[str, Sequence[Optional[Union[float,int]]]]]) -> None:
    fig, axs = plt.subplots()
    plot_data = []
    names = []
    for (name, data) in all_data:
        tdata = [(x if x is not None else -1.0) for x in data]
        r = max(tdata) - min(tdata)
        ndata = [(x - min(tdata)) / r for x in tdata]
        plot_data.append(ndata)
        names.append(name)
    axs.violinplot(plot_data)
    axs.set_xticks(list(range(1, len(names)+1)))
    axs.set_xticklabels(names)
    plt.show()


def times(l: Sequence[Optional[Union[float, Tuple[float, int]]]]) -> Sequence[Optional[float]]:
    return [x[0] if x is not None and isinstance(x, tuple) else x for x in l]


def nqueries(l: Sequence[Optional[Union[float, Tuple[float, int]]]]) -> Sequence[Optional[int]]:
    return [x[1] if x is not None and isinstance(x, tuple) else None for x in l]

all_data: List[Tuple[str, Sequence[Tuple[str, Sequence[Union[float, Tuple[float, int], None]]]]]]
transformed_data: Sequence[Tuple[str, Sequence[Tuple[str, Sequence[Optional[float]]]]]]
def main() -> None:
    global all_data
    all_data = []
    for fn in args.filename:
        with open(fn) as f:
            all_data.append((fn, get_all_matching_data(f, args.benchmark or "Benchmark", args.exclude)))

    transform: Callable[[Sequence[Union[float, Tuple[float, int], None]]], Sequence[Optional[Union[float,int]]]]
    if args.column == 'nqueries':
        transform = nqueries
    else:
        assert args.column == 'time'
        transform = times

    global transformed_data
    transformed_data = [(nm, [(b, transform(l)) for b, l in run]) for nm, run in all_data]

    if args.action == 'plot':
        hist(transformed_data)
    elif args.action == 'pdb':
        pdb.set_trace()
    elif args.action == 'extract':
        for nm, run in transformed_data:
            print(nm)
            for b, d in run:
                print(' ', b)
                print(' ', d)
    elif args.action == 'argmax':
        for nm, run in transformed_data:
            print(nm)
            for b, d in run:
                d = [x or np.NINF for x in d]
                print(' ', b)
                i = np.argmax(d)
                print(' ', i, d[i])
    else:
        assert args.action == 'nop'

args: argparse.Namespace

if __name__ == '__main__':
    print(' '.join(['python3'] + sys.argv))

    argparser = argparse.ArgumentParser()

    argparser.add_argument('--benchmark')
    argparser.add_argument('--exclude')
    argparser.add_argument('--column', default='nqueries', choices=['nqueries', 'time'])
    argparser.add_argument('--action', default='plot', choices=['plot', 'argmax', 'pdb', 'extract', 'nop'])
    argparser.add_argument('filename', nargs='+')

    args = argparser.parse_args()

    main()
