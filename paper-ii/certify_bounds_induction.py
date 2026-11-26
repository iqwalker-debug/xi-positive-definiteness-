"""Smallest real roots of P_m for 1 <= m <= 20 (odd dimensions 3 to 41) by monotone induction (python-flint 0.9.0).

P_m(lam) = (-1)^m * sum_j a_j lam^(m-j)/(m-j)!,  a_j = Phi^(2j)(0)/(2j)!,  and P_m' = -P_(m-1).

For each m the program proves, in ball arithmetic at exact rational points only:
  (1) a bracket [lo_m, hi_m] of width 2e-12 with P_m(lo_m) > 0 > P_m(hi_m);
  (2) hi_m < lo_(m-1) for m >= 2;
  (3) the same two signs at the ends of the rounding cell of the printed eleven-decimal value.
Induction. P_0 = a_0 > 0. Suppose P_(m-1) > 0 to the left of its smallest real root lam_(m-1), which lies
in (lo_(m-1), hi_(m-1)) (for m = 1, on all of R). Then P_m is strictly decreasing on (-inf, lam_(m-1)].
By (1) and (2) it has exactly one root there, inside (lo_m, hi_m); it is positive to the left of that root
and negative from it up to lam_(m-1). No interval cover of a half-line is needed, which is what limits
certify_bounds.py to m <= 13 (its cover next to the root fails at m = 15).
The first thirteen brackets must equal those of heat-upper-bounds.json.
"""
if not __debug__:
    raise SystemExit("Verification requires Python assertions. Remove -O or PYTHONOPTIMIZE.")

from fractions import Fraction as F
import json
from flint import arb, ctx
from mpmath import mp, mpf, polyroots

MMAX = 20


def ball(x):
    x = F(x); return arb(x.numerator) / x.denominator


def run(bits):
    ctx.prec = bits
    pi = arb.pi()
    K = 2*MMAX
    polys = [[F(0), F(-3), F(2)]]
    for _ in range(K):
        old = polys[-1]
        polys.append([(F(1,2)+2*j)*(old[j] if j < len(old) else 0) - (2*old[j-1] if j else 0)
                      for j in range(len(old)+1)])
    # Tail n >= N of Phi^(k)(0), exactly as in certify_bounds.py, with a larger N.
    N = 20
    XN = pi*N*N
    assert XN > 2*(K+2)
    der = {}
    for k in range(0, K+1, 2):
        C = sum(abs(c) for c in polys[k])
        tail = ball(C) * XN**(k+2) * (-XN/2).exp() * 2 * (-XN/2).exp()
        s = arb(0, tail.upper())
        for n in range(1, N):
            x = pi*n*n
            p = arb(0)
            for c in reversed(polys[k]):
                p = p*x + ball(c)
            s += (-x).exp()*p
        der[k] = s
    fact = [arb(1)]
    for i in range(1, K+2): fact.append(fact[-1]*i)
    a = [der[2*j]/fact[2*j] for j in range(MMAX+1)]
    assert a[0] > 0                                       # P_0 > 0

    def P(m, lam):
        lam = ball(lam); p = arb(0)
        for j in range(m+1):
            p = p*lam + (a[j]/fact[m-j]) * (1 if m % 2 == 0 else -1)
        return p

    out = []
    prev_lo = None
    for m in range(1, MMAX+1):
        # floating guess for the smallest real root (not trusted; only used to choose rationals)
        mp.dps = 120
        fl = [mpf(((a[j]/fact[m-j]) * (1 if m % 2 == 0 else -1)).mid().str(110, radius=False)) for j in range(m+1)]
        rs = sorted(z.real for z in polyroots(fl, maxsteps=2000, extraprec=2000) if abs(z.imag) < mpf(10)**-40)
        g = rs[0]
        lo = F(int(g*10**12) - 1 - (1 if g < 0 else 0), 10**12); hi = lo + F(2, 10**12)
        assert P(m, lo) > 0 and P(m, hi) < 0, (m, 'bracket')
        if prev_lo is not None:
            assert hi < prev_lo, (m, 'ordering')
        printed = F(int(mp.nint(g*10**11)), 10**11)
        cell_lo, cell_hi = max(lo, printed - F(5, 10**12)), min(hi, printed + F(5, 10**12))
        assert cell_lo < cell_hi and P(m, cell_lo) > 0 and P(m, cell_hi) < 0, (m, 'eleven-decimal rounding')
        out.append(dict(dimension=2*m+1, m=m, lower=str(lo), upper=str(hi), rounded=f"{float(printed):.11f}"))
        prev_lo = lo
    return dict(precision=bits, results=out)


if __name__ == '__main__':
    res = [run(b) for b in (512, 768)]
    assert res[0]['results'] == res[1]['results']
    old = json.load(open('heat-upper-bounds.json'))[0]['results']
    assert [(F(o['lower']), F(o['upper'])) for o in old] == \
           [(F(o['lower']), F(o['upper'])) for o in res[0]['results'][:len(old)]], 'brackets differ from heat-upper-bounds.json'
    for o in res[1]['results']:
        print('D%d' % o['dimension'], o['rounded'])
    with open('heat-upper-bounds-extended.json', 'w') as f: json.dump(res, f, indent=1)
    print('OK')
