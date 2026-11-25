"""Full finite D10 Gram witness via Arb/ACB. No omitted-distance majorant."""
import argparse
import json
import re
from fractions import Fraction
from pathlib import Path

from flint import acb, arb, ctx

WEIGHTS = [282, 541, 756, 910, 990, 990, 910, 756, 541, 282]
DIMENSION, SPACING, SPLIT, SCALE = 10, 7, 293, 10**18


def histogram():
    single = [0] * 82
    for i, a in enumerate(WEIGHTS):
        for j, b in enumerate(WEIGHTS):
            single[(i - j) ** 2] += a * b
    coeff = [1]
    for _ in range(DIMENSION):
        nxt = [0] * (len(coeff) + 81)
        for j, b in enumerate(single):
            if b:
                for i, a in enumerate(coeff):
                    nxt[i + j] += a * b
        coeff = nxt
    if sum(coeff) != sum(WEIGHTS) ** (2 * DIMENSION):
        raise ArithmeticError("coefficient mass mismatch")
    return coeff, single[0] ** DIMENSION


def xi(t):
    s = acb(arb(1) / 2, t)
    return ((s * (s - 1) / 2) * (s / 2).gamma()
            * (-s / 2 * arb.pi().log()).exp() * s.zeta()).real


def outward(ball, upper):
    edge = ball.upper() if upper else ball.lower()
    mantissa, exponent = (int(a) for a in edge.man_exp())
    q = Fraction(mantissa) * Fraction(2) ** exponent * SCALE
    return -((-q.numerator) // q.denominator) if upper else q.numerator // q.denominator


def certify(bits):
    ctx.prec = bits
    coeff, norm = histogram()
    base = xi(arb(0))
    if not base > 0:
        raise ArithmeticError("central xi is not certified positive")
    rows = []
    for k, c in enumerate(coeff):
        if not c:
            continue
        value = (arb(c) / norm) * (xi(SPACING * arb(k).sqrt()) / base)
        rows.append(dict(index=k, coefficient=str(c), lower=outward(value, False),
                         upper=outward(value, True)))
    retained = [r for r in rows if r["index"] <= SPLIT]
    remainder = [r for r in rows if r["index"] > SPLIT]
    bounds = lambda group: [sum(r[key] for r in group) for key in ("lower", "upper")]
    r, o, total = bounds(retained), bounds(remainder), bounds(rows)
    if not (len(rows) == 739 and len(retained) == 294 and total[1] < 0
            and r[1] <= -125963671 * (SCALE // 10**10)
            and o[1] <= SCALE // 10**9):
        raise ArithmeticError("expected certificate inequalities not met")
    return dict(bits=bits, normalization=str(norm), scale=SCALE, retained=r, omitted=o,
                total=total, rows=rows)


def check_lean_rows(result, source):
    for name, want_retained in (("retainedUnits", True), ("omittedUnits", False)):
        m = re.search(rf"def {name} : List ℤ := \[([^\]]+)\]", source)
        if m is None:
            raise ArithmeticError(f"cannot find {name} in Lean source")
        reported = [int(x) for x in m[1].split(",")]
        expected = [r["upper"] for r in result["rows"]
                    if (r["index"] <= SPLIT) == want_retained]
        if reported != expected:
            raise ArithmeticError(f"{name} differs from fresh Arb replay")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--bits", type=int, default=192)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--check-lean", type=Path)
    args = ap.parse_args()
    result = certify(args.bits)
    if args.check_lean:
        check_lean_rows(result, args.check_lean.read_text())
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print({k: v for k, v in result.items() if k != "rows"})
