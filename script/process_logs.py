from lxml import etree
import os
import sys
from typing import Tuple, Optional

def traverse(e: etree.Element) -> Optional[Tuple[float, float]]:
    lo = e.get('time')
    hi = lo
    for child in e:
        ans = traverse(child)
        if ans is not None:
            a, b = ans
            if lo is None:
                lo = a
            hi = b

    if lo is not None:
        assert hi is not None
        e.set('begin', lo)
        e.set('end', hi)
        e.set('duration', str(round(float(hi) - float(lo), 3)))
        return (lo, hi)
    else:
        return None

def main() -> None:
    if len(sys.argv) != 2:
        print('expected exactly one argument (filename)')
        sys.exit(1)

    infile = sys.argv[1]
    tree = etree.parse(infile)
    root = tree.getroot()

    traverse(root)

    outfile = os.path.splitext(infile)[0] + '-processed.xml'
    print(outfile)
    tree.write(outfile)

if __name__ == '__main__':
    main()
