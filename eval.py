import sys
import matplotlib.pyplot as plt  # type: ignore
import math
import numpy as np  # type: ignore

from typing import List, Optional, Tuple, TextIO, Union, Sequence

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



def hist(all_data: Sequence[Tuple[str, Sequence[Optional[Union[float,int]]]]]) -> None:
    length = len(all_data)
    ncols = math.ceil(math.sqrt(length))
    nrows = math.ceil(length / ncols)

    fig, axs = plt.subplots(nrows, ncols)

    dims = [(i, j) for i in range(nrows) for j in range(ncols)]

    for k, (bname, data) in enumerate(all_data):
        tdata = [(x if x is not None else -1.0) for x in data]

        i, j = dims[k]

        axs[i][j].hist(tdata, bins=80)
        axs[i][j].set_title(bname)

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

def main(filename: str, benchmark: Optional[str]) -> None:
    with open(filename) as f:
        all_data = get_all_matching_data(f, benchmark or "Benchmark")

    hist([(b, nqueries(l)) for b, l in all_data])

    # violin(all_data)



if __name__ == '__main__':
    print(sys.argv)

    if len(sys.argv) < 2:
        print('expected at least one argument (filename)')
        sys.exit(1)

    benchmark: Optional[str]
    if len(sys.argv) >= 3:
        benchmark = sys.argv[2]
    else:
        benchmark = None

    main(sys.argv[1], benchmark)
