from __future__ import annotations
import argparse
import matplotlib.pyplot as plt  # type: ignore
import math
import numpy as np  # type: ignore
import pdb
import sys
from typing import List, Optional, Tuple, TextIO, Union, Sequence, Any, Callable

def get_all_matching_data(buf: TextIO, pattern: str) -> Sequence[Tuple[str, Sequence[Optional[Union[float, Tuple[float, int]]]]]]:
    matched = False
    benchmark_name = ''
    data = []
    for line in buf:
        if matched:
            data.append((benchmark_name, eval(line)))
            matched = False
        if pattern in line:
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


def hist(all_data: Sequence[Tuple[str, Sequence[Optional[Union[float,int]]]]]) -> None:
    length = len(all_data)
    ncols = math.ceil(math.sqrt(length))
    nrows = math.ceil(length / ncols)

    fig, axs = plt.subplots(nrows, ncols)

    dims = [(i, j) for i in range(nrows) for j in range(ncols)]

    for k, (bname, data) in enumerate(all_data):
        tdata = [(x if x is not None else -1.0) for x in data]

        i, j = dims[k]

        a = index(axs, nrows, ncols, i, j)
        a.hist(tdata, bins=80)
        a.set_title(bname)

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

def main() -> None:
    with open(args.filename) as f:
        all_data = get_all_matching_data(f, args.benchmark or "Benchmark")

    transform: Callable[[Sequence[Union[float, Tuple[float, int], None]]], Sequence[Optional[Union[float,int]]]]
    if args.column == 'nqueries':
        transform = nqueries
    else:
        assert args.column == 'time'
        transform = times

    td = [(b, transform(l)) for b, l in all_data]

    if args.action == 'plot':
        hist(td)
    elif args.action == 'pdb':
        pdb.set_trace()
    elif args.action == 'extract':
        for b, d in td:
            print(b)
            print(d)
    else:
        assert args.action == 'argmax'
        for b, d in td:
            d = [x or np.NINF for x in d]
            print(b)
            i = np.argmax(d)
            print(i, d[i])

args: argparse.Namespace

if __name__ == '__main__':
    print(' '.join(['python3'] + sys.argv))

    argparser = argparse.ArgumentParser()

    argparser.add_argument('--benchmark')
    argparser.add_argument('--column', default='nqueries', choices=['nqueries', 'time'])
    argparser.add_argument('--action', default='plot', choices=['plot', 'argmax', 'pdb', 'extract'])
    argparser.add_argument('filename')

    args = argparser.parse_args()

    main()
