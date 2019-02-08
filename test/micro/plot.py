import csv
import sys
import os

from typing import Tuple, Sequence

Range = Tuple[float, float]
Point2d = Tuple[float, float]
Range2d = Tuple[Range, Range]

class LinearTransform(object):
    def __init__(self, irange: Range, orange: Range) -> None:
        self.irange = irange
        self.orange = orange

    def __call__(self, x: float) -> float:
        assert self.irange[0] <= x and x <= self.irange[1], x
        def length(r: Range) -> float:
            return float(r[1] - r[0])

        nx = (x - self.irange[0]) / length(self.irange)
        return round(nx * length(self.orange) + self.orange[0], 3)

class LinearTransform2d(object):
    def __init__(self, irange: Range2d, orange: Range2d) -> None:
        self.xt = LinearTransform(irange[0], orange[0])
        self.yt = LinearTransform(irange[1], orange[1])

    def __call__(self, p: Point2d) -> Point2d:
        return (self.xt(p[0]), self.yt(p[1]))

def prelude() -> None:
    print(r'''
\documentclass{standalone}
\usepackage{tikz}
\begin{document}
\begin{tikzpicture}[
    lbl/.style={font=\sffamily\scriptsize}
]
    ''')

def postlude() -> None:
    print(r'''
\end{tikzpicture}
\end{document}
    ''')


def draw_line(a: Point2d, b: Point2d, opts: str='') -> None:
    print(r'\draw[{}] {} -- {};'.format(opts, a, b))

def fill_circle(c: Point2d, opts: str='', draw_opts: str='') -> None:
    print(r'\fill[{}] {} circle [{}];'.format(draw_opts, c, opts))

Data = Sequence[Tuple[str, Sequence[Point2d]]]

def plot(series: Data) -> None:
    screenx = (0, 4)
    screeny = (0, 3)
    xrange = (1.5,11)
    yrange = (0,450)

    t = LinearTransform2d((xrange, yrange), (screenx, screeny))

    print(r'\draw[->] (-0.1, 0) -- node[lbl,below=3mm] {{{}}} {};'.format('protocol rounds', (screenx[1], 0)))
    for x in range(2,11):
        print(r'\draw ({}, -0.05) -- node[lbl,below] {{{}}} ({}, 0.05);'.format(t.xt(x), x, t.xt(x)))

    print(r'\draw[->] (0, -0.1) -- node[lbl,above=6mm,sloped] {{{}}} {};'.format('run time (s)', (0, screeny[1])))
    for y in range(100,401, 100):
        print(r'\draw (-0.05, {}) -- node[lbl,left] {{{}}} (0.05, {});'.format(t.yt(y), y, t.yt(y)))


    for name, data in series:
        prev = None
        for r in data:
            fill_circle(t(r), 'radius=1pt')
            if prev is not None:
                draw_line(t(prev), t(r))
            prev = r

        assert prev is not None
        print(r'\path {} node[lbl,right] {{{}}};'.format(t(prev), name))


def load(f: str) -> Sequence[Point2d]:
    return [(int(r[0]), float(r[1])) for r in csv.reader(open(f, 'r'))]

def main() -> None:
    logdir = sys.argv[1]

    long = ("automaton(long)", load(os.path.join(logdir, 'automaton_long.csv')))
    short = ("automaton(short)", load(os.path.join(logdir, 'automaton_short.csv')))
    updr = ("updr", load(os.path.join(logdir, 'updr.csv')))

    prelude()
    plot([long, short, updr])
    postlude()

if __name__ == '__main__':
    main()
