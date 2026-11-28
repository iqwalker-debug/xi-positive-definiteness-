"""Certify strict negativity of Paper I's fixed D10 test for 0 <= lambda <= 1.
All bounds concern the unnormalized integral on the positive half-line.
See D10-heat-witness.md for the quadrature and tail inequalities.
"""
from math import factorial
from pathlib import Path
import sys

from flint import arb, ctx

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "verification" / "arb"))
from certify_finite import DIMENSION, SPACING, histogram


def check(ok, message):
    if not ok:
        raise ArithmeticError(message)


def verify(bits):
    ctx.prec = bits
    coeff, norm = histogram()
    freq = [(SPACING * arb(i).sqrt(), arb(c) / norm) for i, c in enumerate(coeff) if c]
    total = arb(sum(coeff)) / norm
    pi = arb.pi()
    radius = arb(1) / 8
    panels, order, degree = 128, 16, 48
    h = arb(1) / panels
    ratio = h / radius
    one = arb(1)
    e = one.exp()

    # Complex Cauchy bound on each panel disk, simultaneously in lambda.
    xmax = pi * (2 * (2 + radius)).exp()
    xmin = pi * (-2 * radius).exp() * (2 * radius).cos()
    check(xmin > 2, "complex theta decay")
    phi_max = 2 * ((2 + radius) / 2).exp() * xmax * (2*xmax + 3) / (e - 1)
    analytic_max = (total * (freq[-1][0] * radius).exp() * phi_max
                    * ((2 + radius)**2).exp())
    quadrature_error = 4 * analytic_max * ratio**(2*order) / (1-ratio)

    # For r>=2, split X/2 into two quarters (see the accompanying proof).
    check(pi > 3 and pi * arb(4).exp() / 4 > 41, "tail constants")
    tail_error = 16 * total * arb(-42).exp() / (e-1)

    nodes = [arb.legendre_p_root(order, j, weight=True) for j in range(order)]
    sums = [arb(0) for _ in range(degree+1)]
    magnitude = arb(0)
    n0 = 13
    omitted_phi = 16*e*arb(-n0*n0-n0).exp() / (1-1/e)
    for panel in range(panels):
        center = (2*panel+1)*h
        for a, w in nodes:
            r = center + h*a
            r2 = r*r
            z = pi*(2*r).exp()
            phi = arb(0, omitted_phi.upper())
            for n in range(1, n0):
                x = z*n*n
                phi += (r/2-x).exp() * x * (2*x-3)
            q = sum((v * (t*r).cos() for t, v in freq), arb(0))
            v = h*w*phi*q
            magnitude += abs(v)
            for j in range(degree+1):
                sums[j] += v
                v = v*r2/(j+1)

    remainder = magnitude*arb(4).exp()*arb(4)**(degree+1)/factorial(degree+1)
    error = quadrature_error + tail_error + remainder
    upper = -arb(1)/1000
    for k in range(256):
        s = (arb(k)/256).union(arb(k+1)/256)
        p = sums[-1]
        for b in reversed(sums[:-1]):
            p = b + s*p
        check(p + error < upper, f"parameter cell {k} at {bits} bits")
    print(f"PASS {bits} bits; D{DIMENSION}; {len(freq)} frequencies; 256 parameter intervals; "
          f"unnormalized half-integral < -1/1000; quadrature error {quadrature_error}; "
          f"tail error {tail_error}; parameter-series error {remainder}", flush=True)


if __name__ == "__main__":
    for precision in (192, 256):
        verify(precision)
