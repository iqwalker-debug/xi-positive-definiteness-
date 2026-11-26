"""Every certified witness must occur in both continuous upper enclosures."""
import csv
import sys
from bisect import bisect_left, bisect_right
from fractions import Fraction
from pathlib import Path

def check(paths):
    edges = [1 - Fraction(1,2**j) + Fraction(i,128*2**(j+1))
             for j in range(1,17) for i in range(128)] + [1-Fraction(1,2**17),Fraction(1)]
    masks = [p.read_bytes() for p in paths]
    width = 2**18//8
    if any(len(buf) != (len(edges)-1)*width for buf in masks):
        raise ValueError("Wrong partition size")
    witnesses = {}
    base = Path(__file__).resolve().parent
    for name in ("witnesses.csv", "five-witnesses.csv", "combined-witnesses.csv"):
        with (base/name).open() as rows:
            for m,b in csv.reader(rows):
                witnesses.setdefault(int(b),set()).add(int(m))
    checked = 0
    for b, indices in witnesses.items():
        z = Fraction(b-1,b)
        lo = max(0,bisect_left(edges,z)-1)
        hi = min(len(edges)-1,bisect_right(edges,z))
        if lo>=hi: raise ValueError("Witness outside partition")
        for i in range(lo,hi):
            for buf in masks:
                for m in indices:
                    if not (buf[i*width + m//8] & (1<<(m%8))):
                        raise ArithmeticError((b,i,m))
                    checked += 1
    print(f"{sum(map(len,witnesses.values()))} distinct (mask, denominator) pairs at {len(witnesses)} points; {checked} enclosure inclusions passed.")

if __name__=="__main__":
    check([Path(sys.argv[1]),Path(sys.argv[2])])
