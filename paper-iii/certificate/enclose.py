"""Construct rigorous supersets of potentially certifiable patterns over intervals of z."""
import argparse
import hashlib
from pathlib import Path
import numpy as np

PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61)
PATTERNS = 1 << len(PRIMES)
N = 300
S = 1 << 46

def parity_key(n):
    key = 0
    for i, p in enumerate(PRIMES):
        while n % p == 0:
            n //= p
            key ^= 1 << i
    return key if n == 1 else None

def rounded_power(x, k):
    # x is an exact endpoint in units of S. All scalar arithmetic is unbounded.
    lo = hi = S
    a = b = x
    while k:
        if k & 1:
            lo = lo*a//S
            hi = (hi*b+S-1)//S
        a = a*a//S
        b = (b*b+S-1)//S
        k >>= 1
    return lo, hi

def endpoint(x, keys):
    center = np.zeros(PATTERNS, dtype=np.int64)
    constant = error = curvature_num = 0
    for n, key in enumerate(keys, start=1):
        k = n*n
        lo, hi = rounded_power(x, k)
        if key is None:
            constant += n*lo
        else:
            center[key] += n*lo
            error += n*(hi-lo)
        curvature_num += n*k*(k-1)*hi
    length = 1
    while length < PATTERNS:
        blocks = center.reshape(-1, 2, length)
        a = blocks[:, 0].copy()
        b = blocks[:, 1]
        blocks[:, 0] = a+b
        b[:] = a-b
        length *= 2
    center += constant-error
    return center, curvature_num

def build(subdivisions, path):
    if subdivisions < 1 or subdivisions & (subdivisions-1) or subdivisions > 32768:
        raise ValueError("subdivisions must be a power of two from 1 to 32768")
    points = []
    for j in range(1, 17):
        start = S - (S >> j)
        width = S >> (j+1)
        points.extend(start + i*(width//subdivisions) for i in range(subdivisions))
    points.extend([S-(S>>17), S])
    keys = [parity_key(n) for n in range(1, N+1)]
    previous, _ = endpoint(points[0], keys)
    with path.open("wb") as out:
        for left, right in zip(points, points[1:]):
            current, curv = endpoint(right, keys)
            # Interpolation loss in units of S is <= curv*(right-left)^2/(8*right^2).
            num, den = curv*(right-left)**2, 8*right**2
            loss = (num + den - 1)//den
            possible = np.minimum(previous,current) < loss
            out.write(np.packbits(possible, bitorder="little").tobytes())
            previous = current
    print(f"{len(points)-1} interval masks, SHA-256 {hashlib.sha256(path.read_bytes()).hexdigest()}", flush=True)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", type=Path)
    parser.add_argument("--subdivisions", type=int, default=128)
    args = parser.parse_args()
    build(args.subdivisions,args.path)
