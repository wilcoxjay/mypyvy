import sys
import matplotlib.pyplot as plt  # type: ignore
import math
import numpy as np  # type: ignore

from typing import List, Optional, Tuple, TextIO

def get_all_matching_data(buf: TextIO, pattern: str) -> List[Tuple[str, List[Optional[float]]]]:
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



def main(filename: str, benchmark: Optional[str]) -> None:
    with open(filename) as f:
        all_data = get_all_matching_data(f, benchmark or "Benchmark")

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
