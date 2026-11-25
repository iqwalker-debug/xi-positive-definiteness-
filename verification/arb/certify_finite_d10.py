"""Arb replay of the concrete finite Gram witness.

Both parts of the finite sum are evaluated directly. No analytic tail
bound or theta/Fourier identity is used.
"""
import json
import sys

import flint
from flint import acb, arb, ctx

ctx.prec = int(sys.argv[1]) if len(sys.argv) > 1 else 256
WEIGHTS = [282, 541, 756, 910, 990, 990, 910, 756, 541, 282]
SPACING, DIMENSION, TAIL_START = 7, 10, 120


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def xi(t):
    s = acb(arb(1) / 2, t)
    return (s * (s - 1) / 2 * (s / 2).gamma()
            * (-s / 2 * arb.pi().log()).exp() * s.zeta()).real


def main():
    cutoff = TAIL_START**2 // SPACING**2
    # Same ordered-pair histogram as the Lean witnessPolynomial base.
    p = {}
    for i, a in enumerate(WEIGHTS):
        for j, b in enumerate(WEIGHTS):
            k = (i-j)**2
            p[k] = p.get(k, 0) + a*b
    coeff = [1]
    for _ in range(DIMENSION):
        out = [0] * (len(coeff) + max(p))
        for j, v in p.items():
            for i, u in enumerate(coeff):
                out[i+j] += u*v
        coeff = out
    norm = p[0]**DIMENSION
    require(norm == coeff[0] and sum(coeff) == sum(WEIGHTS)**(2*DIMENSION),
            "coefficient cross-check failed")
    base = xi(arb(0))
    require(base > arb(1)/32, "central normalization check failed")
    values = [arb(c)/norm * xi(SPACING*arb(j).sqrt())/base if c else arb(0)
              for j, c in enumerate(coeff)]
    retained = sum(values[:cutoff+1], arb(0))
    omitted = sum(values[cutoff+1:], arb(0))
    require(retained < -arb(125963671)/10**10, "retained bound inconclusive")
    require(omitted < arb(1)/10**9, "remaining finite sum inconclusive")
    require(retained + omitted < 0, "obstruction inconclusive")
    print(json.dumps({
        "status": "PASS", "python_flint": flint.__version__, "bits": ctx.prec,
        "cutoff_index": cutoff, "max_index": len(coeff)-1,
        "nonzero_coefficients": sum(c != 0 for c in coeff),
        "normalization": norm, "xi_zero": str(base),
        "retained_ball": str(retained), "omitted_ball": str(omitted),
        "total_upper_bound": str((retained + omitted).upper())
    }, indent=2))


if __name__ == "__main__":
    main()
