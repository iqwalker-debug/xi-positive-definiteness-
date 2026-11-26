"""Find the smallest subset of the eleven scales giving a certified majority."""
from itertools import combinations
from functools import reduce
from operator import or_
import json
import certificate18 as c

def scale_mask(b, factor_masks):
    sums = [0] * c.SIZE
    error = 0
    for n, lo, hi in c.enclose_weights(b):
        key = factor_masks[n]
        if key is None:
            error += n * hi
        else:
            sums[key] += n * lo
            error += n * (hi - lo)
    error += (b * hi + 1) // 2
    c.hadamard(sums)
    packed = bytearray(c.SIZE // 8)
    for signs, value in enumerate(sums):
        if value + error < 0:
            packed[signs // 8] |= 1 << (signs % 8)
    return int.from_bytes(packed, "little")

def main():
    keys = [None] + [c.factor_mask(n) for n in range(1, c.N + 1)]
    masks = {b: scale_mask(b, keys) for b in c.SCALES}
    if reduce(or_, masks.values()).bit_count() != 132606:
        raise ArithmeticError("Full-grid count differs from the replay.")
    best = []
    for size in range(1, len(masks) + 1):
        candidates = ((reduce(or_, (masks[b] for b in grid)).bit_count(), grid)
                      for grid in combinations(c.SCALES, size))
        count, grid = max(candidates)
        best.append(dict(size=size, count=count, scales=grid))
        if count > c.SIZE // 2:
            break
    print(json.dumps(best, indent=2))

if __name__ == "__main__":
    main()
