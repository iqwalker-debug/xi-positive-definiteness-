"""Emit a standalone Lean proof using integer Bernstein certificates on dyadic cells."""
from fractions import Fraction
from math import lcm, comb
from pathlib import Path
import sys

import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from verify import EXCLUDED, FEASIBLE

x = sp.symbols("x")
lines = ["import data.real.basic", "import tactic", "namespace paper_v", ""]


def coefficients(poly, left, right):
    q = lcm(left.denominator, right.denominator)
    a, b = int(left*q), int(right*q)
    # Expand q^6(s+t)^6 p((a*t+b*s)/(q*(s+t))).
    coeffs = [sum(int(poly.nth(k))*q**(6-k)*comb(k, j)*a**(k-j)*b**j*comb(6-k, i-j)
                  for k in range(7) for j in range(max(0, i-6+k), min(i,k)+1))
              for i in range(7)]
    return a, b, q, coeffs


def cell(poly, left, right, name):
    a, b, q, coeffs = coefficients(poly, left, right)
    prefix = ["lemma " + name + " (x : ℝ)", f"  (hl : ({a}:ℝ) ≤ {q}*x) (hr : {q}*x ≤ ({b}:ℝ)) :", "  0 ≤ " + current + " x :=", "begin"]
    if min(coeffs) < 0:
        mid = (left+right)/2
        cell(poly, left, mid, name+"l")
        cell(poly, mid, right, name+"r")
        lines.extend(prefix + [f"  by_cases h : {mid.denominator}*x ≤ ({mid.numerator}:ℝ),",
                               f"  {{ apply {name}l x; linarith }},",
                               f"  {{ apply {name}r x; linarith }},", "end", ""])
        return
    expr = " + ".join(f"{v}*s^{i}*t^{6-i}" for i,v in enumerate(coeffs) if v)
    lines.extend(prefix + [f"  let s := {q}*x - ({a}:ℝ),", f"  let t := ({b}:ℝ) - {q}*x,",
                           "  have hs : 0 ≤ s := sub_nonneg.mpr hl,", "  have ht : 0 ≤ t := sub_nonneg.mpr hr,",
                           f"  have h : 0 ≤ {expr} := by positivity,",
                           f"  have e : {expr} = {q**6*(b-a)**6} * {current} x := by dsimp [s,t,{current},T]; ring,",
                           "  rw [e] at h, linarith only [h],", "end", ""])


lines.extend(["def T (x : ℝ) : ℕ → ℝ", "| 0 := 1", "| 1 := x",
              "| (n+2) := 2*x*T (n+1) - T n", ""])
for j,(coeffs,u) in enumerate(EXCLUDED):
    for sign in [-1,1]:
        current = f"row{j+1}_" + ("minus" if sign == -1 else "plus")
        weights = list(coeffs)
        weights[1] += sign*u
        weights[2] += sign*(200000-u)
        poly = sp.Poly(sum(v*sp.chebyshevt(i,x) for i,v in enumerate(weights)), x)
        expr = " + ".join(f"({v}:ℝ)*T x {i}" for i,v in enumerate(weights) if v)
        lines.extend([f"def {current} (x : ℝ) := {expr}", ""])
        cell(poly,Fraction(-1),Fraction(1),current+"_nonneg")
        lines.append("#print axioms "+current+"_nonneg")

# Direct test of all 64 Boolean inputs, linked to the same certificate supports.
def predicate(rows, feasible):
    terms = []
    for row in rows:
        terms.append("("+" ∧ ".join(f"b{j} = "+("ff" if feasible else "tt") for j in sorted(row))+")")
    return " ∨ ".join(terms)

yes = predicate([m for m,_ in FEASIBLE], True)
no = predicate([{i for i,c in enumerate(r) if i and c} for r,_ in EXCLUDED], False)
lines.extend(["", "theorem covers_exactly (b1 b2 b3 b4 b5 b6 : bool) :",
              f"  ({yes}) ↔ ¬ ({no}) :=",
              "by cases b1; cases b2; cases b3; cases b4; cases b5; cases b6; dec_trivial",
              "#print axioms covers_exactly", "end paper_v"])
(ROOT/"formal"/"Certificates.lean").write_text("\n".join(lines)+"\n")
