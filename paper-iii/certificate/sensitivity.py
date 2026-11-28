"""Check two fixed grids with the first 17 prime signs and the n=300 rule."""
from certificate18 import N, PRIMES, enclose_weights, hadamard


def parity_key(n, primes):
    key = 0
    for index, prime in enumerate(primes):
        while n % prime == 0:
            n //= prime
            key ^= 1 << index
    return key if n == 1 else None


def mask_bounds(denominators, primes):
    keys = [parity_key(n, primes) for n in range(1, N + 1)]
    certified = set()
    possible = set()
    for b in denominators:
        assert 2 * N * N >= b
        centers = [0] * (1 << len(primes))
        smooth_error = unknown_lower = unknown_upper = 0
        for n, lo, hi in enclose_weights(b):
            key = keys[n - 1]
            if key is None:
                unknown_lower += n * lo
                unknown_upper += n * hi
            else:
                centers[key] += n * lo
                smooth_error += n * (hi - lo)
        hadamard(centers)
        # hi encloses the final power z^(N*N), in the verifier's units.
        tail_upper = (b * hi + 1) // 2
        for mask, center in enumerate(centers):
            if center + smooth_error + unknown_upper + tail_upper < 0:
                certified.add(mask)
            # Acceptance implies negativity of the finite upper polynomial.
            if center - smooth_error + unknown_lower < 0:
                possible.add(mask)
    return certified, possible


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Enable assertions for verification.")
    for grid, count in [((4, 52, 212, 695, 1438), 65301),
                        ((4, 52, 210, 685, 1286), 65360)]:
        certified, possible = mask_bounds(grid, PRIMES[:-1])
        assert certified == possible and len(certified) == count
        print(f"17 signs, b={grid}: {count} certified; finite upper set matches.")
