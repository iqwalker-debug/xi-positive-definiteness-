"""Bound the union of four interval-mask sets by exhaustive branch and bound."""
import argparse
from pathlib import Path

PATTERNS = 1 << 18
BYTES = PATTERNS // 8

def prove(path, limit, verbose=False):
    data = path.read_bytes()
    if not data or len(data) % BYTES:
        raise ValueError("Incomplete mask file")
    masks = []
    children = []
    representative = []
    def add(mask, pair, index):
        masks.append(mask)
        children.append(pair)
        representative.append(index)
        return len(masks)-1
    level = [add(int.from_bytes(data[i:i+BYTES], 'little'), None, i//BYTES)
             for i in range(0,len(data),BYTES)]
    while len(level)>1:
        nxt = []
        for i in range(0,len(level),2):
            a = level[i]
            if i+1 == len(level):
                nxt.append(a)
                continue
            b = level[i+1]
            union = masks[a] | masks[b]
            if children[a] is None and union == masks[a]:
                nxt.append(a)
            elif children[b] is None and union == masks[b]:
                nxt.append(b)
            else:
                nxt.append(add(union,(a,b),None))
        level = nxt
    counts = [m.bit_count() for m in masks]
    gain = [(counts[i] - min(counts[a],counts[b])) if pair else -1
            for i,pair in enumerate(children) for a,b in [pair or (0,0)]]
    stack = [(level[0],)*4]
    visited = pruned = failures = worst = 0
    while stack:
        box = stack.pop()
        visited += 1
        a,b,c,d = box
        upper = (masks[a]|masks[b]|masks[c]|masks[d]).bit_count()
        if upper <= limit:
            pruned += 1
            worst = max(worst, upper)
            continue
        node = max(box,key=gain.__getitem__)
        pair = children[node]
        if pair is None:
            failures += 1
            worst = max(worst,upper)
            if failures <= 3 and verbose:
                print("Unresolved box:",[representative[i] for i in box],upper,flush=True)
            continue
        left,right = pair
        fixed = tuple(i for i in box if i!=node)
        positions = 4-len(fixed)
        for j in range(positions+1):
            stack.append(fixed+(left,)*j+(right,)*(positions-j))
    print(f"Boxes visited: {visited}; pruned: {pruned}; unresolved: {failures}; largest terminal upper bound: {worst}",flush=True)
    return failures == 0

if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("path",type=Path)
    p.add_argument("--limit",type=int,default=129903)
    p.add_argument("--verbose",action="store_true")
    a = p.parse_args()
    if not prove(a.path,a.limit,a.verbose):
        raise SystemExit(1)
