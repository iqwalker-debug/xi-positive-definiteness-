"""Verify a lower density bound for failed positive definiteness. Python 3.10+."""
from hashlib import sha256
from fractions import Fraction
import json

PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61)
SCALES = (5, 10, 20, 32, 50, 100, 200, 333, 500, 1000, 2000)
SIZE = 1 << len(PRIMES)
UNIT = 1 << 64
N = 300


def factor_mask(n):
    mask = 0
    for i, prime in enumerate(PRIMES):
        while n % prime == 0:
            n //= prime
            mask ^= 1 << i
    return mask if n == 1 else None


def enclose_weights(b):
    # Endpoints are integers in units of 2^-64. Multiply by (b-1)/b
    # one step at a time, rounding toward minus and plus infinity.
    lo = hi = UNIT
    previous = 0
    for n in range(1, N + 1):
        for _ in range(n*n - previous):
            lo = (lo * (b-1)) // b
            hi = (hi * (b-1) + b-1) // b
        previous = n*n
        yield n, lo, hi


def hadamard(values):
    step = 1
    while step < len(values):
        for offset in range(0, len(values), 2*step):
            for j in range(offset, offset+step):
                left, right = values[j], values[j+step]
                values[j], values[j+step] = left+right, left-right
        step *= 2


def direct_upper_weights(b):
    # Independent enclosure by repeated squaring at a different precision.
    # Obtain signs separately from squarefree kernels via a factor sieve.
    unit = 1 << 80
    def mul(x, y):
        return (x[0]*y[0]//unit, (x[1]*y[1]+unit-1)//unit)
    def power(e):
        x = (unit*(b-1)//b, (unit*(b-1)+b-1)//b)
        acc = (unit, unit)
        while e:
            if e % 2:
                acc = mul(acc, x)
            x = mul(x, x)
            e //= 2
        return acc
    keys = [0]*(N+1)
    smooth = [1]*(N+1)
    for j,p in enumerate(PRIMES):
        q = p
        while q <= N:
            for n in range(q, N+1, q):
                keys[n] ^= 1 << j
                smooth[n] *= p
            q *= p
    terms = []
    error = 0
    for n in range(1, N+1):
        lo, hi = power(n*n)
        if smooth[n] == n:
            terms.append((n*lo,keys[n]))
            error += n*(hi-lo)
        else:
            error += n*hi
    return terms, error + (b*hi+1)//2


def certify():
    masks = [None] + [factor_mask(n) for n in range(1, N+1)]
    witnesses = {}
    cumulative = []
    for b in SCALES:
        assert 2*N*N >= b  # t*z^(t*t) decreases on [N,infinity)
        sums = [0]*SIZE
        error = 0
        direct_terms, direct_error = direct_upper_weights(b)
        for n, lo, hi in enclose_weights(b):
            mask = masks[n]
            if mask is None:
                error += n*hi
            else:
                sums[mask] += n*lo
                error += n*(hi-lo)
        error += (b*hi + 1)//2  # integral tail <= (b/2)*z^(N*N)
        hadamard(sums)
        for signs, value in enumerate(sums):
            if value+error < 0 and signs not in witnesses:
                # Check every accepted witness a second way, directly by signs.
                direct = sum(-w if (signs & mask).bit_count()%2 else w
                             for w, mask in direct_terms)
                if direct+direct_error >= 0:
                    raise ArithmeticError((signs, b))
                witnesses[signs] = b
        cumulative.append(len(witnesses))

    z = Fraction(4, 5)
    simple = z-2*z**4-3*z**9+4*z**16+5*z**25/(1-Fraction(6,5)*z**11)
    assert simple < -Fraction(1,4)
    assert len(witnesses) > SIZE//2
    rows = ''.join(f'{s},{witnesses[s]}\n' for s in sorted(witnesses))
    return witnesses, dict(patterns=SIZE, certified=len(witnesses),
                          cumulative=cumulative, density=str(Fraction(len(witnesses), SIZE)),
                          witnesses_sha256=sha256(rows.encode()).hexdigest())


if __name__ == '__main__':
    print(json.dumps(certify()[1], indent=2))
