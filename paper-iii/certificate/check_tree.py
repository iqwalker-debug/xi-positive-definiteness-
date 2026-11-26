"""Independent exhaustive count: split all four coordinates at each tree level."""
from itertools import product
from pathlib import Path
import sys

def check(path, limit):
    chunks = []
    with path.open("rb") as f:
        for i in range(2049):
            row = f.read(32768)
            if len(row) != 32768:
                raise ValueError("Truncated partition")
            chunks.append(int.from_bytes(row,"little"))
        if f.read(1):
            raise ValueError("Unexpected trailing masks")
    levels = [chunks]
    while len(levels[-1]) > 1:
        layer = levels[-1]
        levels.append([layer[i] | layer[min(i+1,len(layer)-1)] for i in range(0,len(layer),2)])
    pending = {(0,0,0,0)}
    visited = 0
    largest = 0
    for depth in reversed(range(len(levels))):
        layer = levels[depth]
        nxt = set()
        for i,j,k,l in pending:
            visited += 1
            upper = (layer[i] | layer[j] | layer[k] | layer[l]).bit_count()
            if upper <= limit or depth == 0:
                largest = max(largest,upper)
            else:
                choices = [range(2*n,min(2*n+2,len(levels[depth-1]))) for n in (i,j,k,l)]
                nxt.update(tuple(sorted(xs)) for xs in product(*choices))
        pending = nxt
    print(f"Boxes checked: {visited}; largest terminal upper bound: {largest}")
    return largest<=limit

if __name__=="__main__":
    if not check(Path(sys.argv[1]),int(sys.argv[2])):
        raise SystemExit(1)
