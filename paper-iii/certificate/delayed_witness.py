"""An explicit prime family that evades the eleven-point grid and still has a certified negative value.

Sign pattern: chi_p(l) = +1 for primes l <= 43 and chi_p(l) = -1 for primes 47 <= l <= N.
Every n <= N then has a determined sign, for every prime p > N in these classes.
Python 3.10+, standard library only. All bounds are integers in units of 2^-120, rounded outward.
"""
from fractions import Fraction
import json

N = 1500
B = 750000            # test point z = 1 - 1/B, beyond the last grid point 1999/2000
UNIT = 1 << 120


def signs():
    sign = [1] * (N + 1)
    primes = [p for p in range(2, N + 1) if all(p % q for q in range(2, int(p**0.5) + 1))]
    for p in primes:
        if p >= 47:
            q = p
            while q <= N:
                for n in range(q, N + 1, q):
                    sign[n] = -sign[n]
                q *= p
    return sign, len(primes)


def power(e):
    """Integers lo <= UNIT * z^e <= hi by repeated squaring."""
    lo, hi = UNIT * (B - 1) // B, (UNIT * (B - 1) + B - 1) // B
    acc_lo = acc_hi = UNIT
    while e:
        if e & 1:
            acc_lo, acc_hi = acc_lo * lo // UNIT, (acc_hi * hi + UNIT - 1) // UNIT
        lo, hi = lo * lo // UNIT, (hi * hi + UNIT - 1) // UNIT
        e >>= 1
    return acc_lo, acc_hi


def certify():
    sign, prime_count = signs()
    assert all(sign[n] == 1 for n in range(1, 47)) and sign[47] == -1
    # Positivity on (0, 1999/2000]: 45*46 > 1/(-log z0), using log(1+x) > x - x^2/2 at x = 1/1999.
    x = Fraction(1, 1999)
    assert (x - x * x / 2) * 45 * 46 > 1
    assert 2 * N * N >= B                      # t*z^(t*t) decreases on [N, infinity)
    upper = 0
    for n in range(1, N + 1):
        lo, hi = power(n * n)
        upper += n * hi if sign[n] > 0 else -n * lo
    upper += (B * hi + 1) // 2                 # integral tail <= (B/2) * z^(N*N)
    assert upper < 0
    return dict(cutoff=N, denominator=B, prescribed_primes=prime_count,
                relative_density=f"2^-{prime_count}",
                upper_bound=f"{upper}/{UNIT}", upper_bound_decimal=float(Fraction(upper, UNIT)))


if __name__ == "__main__":
    print(json.dumps(certify(), indent=2))
