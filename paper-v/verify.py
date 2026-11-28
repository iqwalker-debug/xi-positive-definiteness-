"""Replay the Paper V certificates from either or both Xi integral formulas."""
import argparse
from itertools import combinations
from pathlib import Path
import sys

import sympy as sp
from flint import acb, arb, arb_mat, ctx

# Reuse the published, tail-bounded quadrature from Paper IV.
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "paper-iv/audit-numeric"))
from matrix import spatial_integral
from formal.generate_fields import CENTERS, ROWS

# For each maximal feasible set: missing equal-time moments and all delayed
# moments, as integer numerators with common denominator 10000.
FEASIBLE = [
    ({2: 5198, 5: -6037}, [5392, 5000, 5000, -1459, 461, -3766, -4216]),
    ({6: -8665}, [-1051, 5000, 5000, 440, -2894, -6856, 789]),
    ({4: 6645}, [-1653, 5000, 5000, 3017, -4431, 3048, 5029]),
    ({3: 4032}, [-789, 5000, 5000, -1188, 974, -104, -291]),
    ({1: 4879}, [2692, 5000, 5000, -54, -2906, -2106, 1935]),
]

# P in Chebyshev coordinates, and the weight on T1 in g = u*T1 + (2-u)*T2.
# Both use denominator 100000. Unused moments have exactly zero coefficient.
EXCLUDED = [
    ([89734, 46883, 7967, 53117, 11076, 0, -8757], 100000),
    ([89470, 50029, 0, 57353, 17221, -8503, -5551], 98880),
]


def xi_moments(method):
    if method == "theta":
        mass = spatial_integral(0)
        return [arb(1)] + [spatial_integral(8*j)/mass for j in range(1, 7)]

    def xi(t):
        s = acb(arb(1)/2, t)
        return s*(s-1)*(s/2).gamma()*s.zeta()*(-s*arb.pi().log()/2).exp()/2

    return [arb(1)] + [(xi(8*j)/xi(0)).real for j in range(1, 7)]


def check(moments):
    indices = set(range(1, 7))
    assert [set(s) for s, _ in ROWS] == [indices - m.keys() for m, _ in FEASIBLE]
    for j in sorted(indices):
        scaled = 1000000*moments[j]
        assert CENTERS[j]-1 < scaled and scaled < CENTERS[j]+1, j
    print("PASS: the six Xi moments satisfy the rational hypotheses of feasible_subsets.")
    yes, no = [], []
    for missing, witness in FEASIBLE:
        equal = [arb(missing[j])/10000 if j in missing else m for j, m in enumerate(moments)]
        delayed = [arb(n)/10000 for n in witness]
        assert witness[1:3] == [5000, 5000]
        for sign in (-1, 1):
            seq = [m + sign*d for m, d in zip(equal, delayed)]
            for size in range(1, 8):
                rows = [[seq[abs(i-j)] for j in range(size)] for i in range(size)]
                assert arb_mat(rows).det() > 0, (missing, sign, size)
        yes.append(indices - missing.keys())

    x = sp.symbols("x")
    for coeffs, u in EXCLUDED:
        p = sum(c*sp.chebyshevt(j, x) for j, c in enumerate(coeffs))
        g = u*x + (200000-u)*sp.chebyshevt(2, x)
        for diff in (p-g, p+g):
            assert diff.subs(x, 0) > 0 and sp.Poly(diff, x).count_roots(-1, 1) == 0
        bound = sum(c*m for c, m in zip(coeffs, moments))/100000
        assert bound < 1
        printed_ceiling = 994643 if coeffs[5] == 0 else 998664
        assert bound < arb(printed_ceiling)/1000000
        active = {j for j in indices if coeffs[j]}
        print("Exclusion", sorted(active), "upper bound", bound)
        no.append(active)

    excluded = []
    for size in range(7):
        for subset in combinations(sorted(indices), size):
            feasible = any(set(subset) <= s for s in yes)
            impossible = any(s <= set(subset) for s in no)
            assert feasible != impossible, subset
            if impossible:
                excluded.append(subset)
    print("Excluded subsets:", excluded)
    assert len(excluded) == 3
    print("PASS: 61 feasible, 3 excluded; minimum size 5, first excluding prefix 6.")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run with Python assertions enabled.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--moments", choices=("xi", "theta", "both"), default="both")
    choice = parser.parse_args().moments
    ctx.prec = 224
    computed = []
    for method in (("xi", "theta") if choice == "both" else (choice,)):
        print("Moment method:", method)
        values = xi_moments(method)
        check(values)
        computed.append(values)
    if len(computed) == 2:
        assert all(a.overlaps(b) for a, b in zip(*computed))
        print("PASS: both Xi moment enclosures overlap at all seven indices.")
