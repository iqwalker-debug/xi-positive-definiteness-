"""Verify the saved derivative bounds on the complete root brackets at 768 bits."""
if not __debug__:
    raise SystemExit("Verification requires Python assertions. Remove -O or PYTHONOPTIMIZE.")

import json
from fractions import Fraction
from math import factorial
from pathlib import Path

from flint import arb, arb_series, ctx


def ball(q):
    q = Fraction(q)
    return arb(q.numerator) / q.denominator


def coefficients():
    # Work in r up to degree 26. The coefficient of r^(2j) is a_j.
    r = arb_series([0, 1])
    density = arb_series([0])
    for n in range(1, 24):
        x = arb.pi() * n*n * (2*r).exp()
        density += (r/2-x).exp() * x * (2*x-3)
    # On |r|=1/8 each omitted summand is bounded by 180 n^4 exp(-2n^2).
    # The geometric tail and Cauchy estimate are detailed in integer/README.md.
    return [density[2*j] + arb(0, ball(Fraction(360 * 8**(2*j), 2**864)))
            for j in range(14)]


def polynomial(a, m, x):
    p = arb(0)
    for j in range(m + 1):
        p = p*x + a[j] / factorial(m-j)
    return (-1)**m * p


def verify():
    ctx.prec, ctx.cap = 768, 27
    a = coefficients()
    # H^(j)(0) = j! a_j. Evaluate y = p'/p - 2 sqrt(p), with p = -(log H)''.
    first = a[1] / a[0]
    second = 2 * a[2] / a[0]
    third = 6 * a[3] / a[0]
    p = first**2 - second
    p_prime = -third + 3 * first * second - 2 * first**3
    assert p > 0
    y = p_prime / p - 2 * p.sqrt()
    assert -8 < y < -7
    print("OK: D5 origin sign certified at 768 bits: -8 < y(0) < -7.")
    blocks = json.loads(Path(__file__).with_name("heat-upper-bounds.json").read_text())
    assert [b["precision"] for b in blocks] == [256, 384]
    for block in blocks:
        assert [row["m"] for row in block["results"]] == list(range(1,14))
        for row in block["results"]:
            m = row["m"]
            lo, hi = ball(row["lower"]), ball(row["upper"])
            assert lo < hi
            # P'_1 is constant. For m >= 2, P''_m=P_(m-2)>0 throughout
            # this particular bracket, so the derivative is maximal at hi.
            if m >= 2:
                assert polynomial(a, m-2, lo.union(hi)) > 0
            maximum = -polynomial(a, m-1, hi)
            stored = Fraction(row["derivative_upper_on_bracket"])
            assert stored.denominator & (stored.denominator - 1) == 0
            assert maximum <= ball(stored) < 0, (block["precision"], m)
    print("OK: 26 exact dyadic upper bounds checked on whole brackets at 768 bits.")


if __name__ == "__main__":
    verify()
