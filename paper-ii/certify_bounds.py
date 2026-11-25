"""Rigorous upper bounds for the odd-dimensional heat endpoints (python-flint 0.9.0).
For d = 2m+1, P_m(lam) = (-1)^m * sum_j a_j lam^(m-j)/(m-j)!, a_j = Phi^(2j)(0)/(2j)!.
Proves, in ball arithmetic:
  (1) an enclosure [lo_m, hi_m] of width 2e-12 with P_m(lo_m) > 0 > P_m(hi_m);
  (2) P_m > 0 on [-B, lo_m], where B is a Cauchy root bound (so lo_m..hi_m holds the smallest real root);
  (3) P_m < 0 on [hi_m, hi_{m-1}]  (no sign return before the previous dimension's endpoint).
"""
from fractions import Fraction as F
import json, sys
from flint import arb, ctx
from mpmath import mp, mpf, polyroots, factorial as mfac

def ball(x):
    x = F(x); return arb(x.numerator) / x.denominator

def run(bits, MMAX=13):
    ctx.prec = bits
    pi = arb.pi()
    K = 2*MMAX
    polys = [[F(0), F(-3), F(2)]]                      # P_0(X) = 2X^2 - 3X, low degree first
    for _ in range(K):
        old = polys[-1]
        polys.append([(F(1,2)+2*j)*(old[j] if j < len(old) else 0) - (2*old[j-1] if j else 0)
                      for j in range(len(old)+1)])
    # Phi^(k)(0) = sum_n exp(-X) P_k(X), X = pi n^2.  Tail n >= N:
    # |P_k(X)| <= C_k X^(k+2) for X >= 1;  X^(k+2) exp(-X/2) is decreasing for X >= 2(k+2);
    # sum_{n>=N} exp(-pi n^2/2) <= 2 exp(-pi N^2/2).
    N = 14
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
    assert a[0] > 0
    out = []
    prev_hi = None
    # D3 (m=1): lam_1 = -a_1/a_0
    for m in range(1, MMAX+1):
        co = [ (a[j]/fact[m-j]) * (1 if m % 2 == 0 else -1) for j in range(m+1) ]   # coeff of lam^(m-j)
        def P(l):
            p = arb(0)
            for c in co: p = p*l + c
            return p
        # floating guess for the smallest real root (not trusted; only used to choose rationals)
        mp.dps = 40
        fl = [mpf(c.mid().str(40, radius=False)) for c in co]
        rs = sorted(z.real for z in polyroots(fl, maxsteps=500, extraprec=400) if abs(z.imag) < mpf(10)**-25)
        g = rs[0]
        lo = F(int(g*10**12) - 1 - (1 if g < 0 else 0), 10**12); hi = lo + F(2, 10**12)
        assert P(ball(lo)) > 0 and P(ball(hi)) < 0, (m, 'bracket')
        # Cauchy bound: all roots satisfy |lam| <= 1 + max |c_i/c_0|
        B = 1 + max(abs(c/co[0]).upper() for c in co[1:])
        Bq = F(int(float(B.str(20, radius=False))) + 2)
        cells = [0, 0]
        def cover(l, r, sign, idx, depth=0):
            v = P(ball(l).union(ball(r)))
            if (v > 0) if sign > 0 else (v < 0):
                cells[idx] += 1; return
            if depth > 70: raise ValueError((m, str(l), str(r), sign))
            mid = (l+r)/2
            cover(l, mid, sign, idx, depth+1); cover(mid, r, sign, idx, depth+1)
        cover(-Bq, lo, +1, 0)
        if prev_hi is not None:
            assert hi < prev_hi
            cover(hi, prev_hi, -1, 1)
        out.append(dict(dimension=2*m+1, m=m, lower=str(lo), upper=str(hi), enclosure=float(lo),
                        cauchy_bound=str(Bq), positive_cells=cells[0], negative_cells=cells[1]))
        prev_hi = hi
    return dict(precision=bits, results=out)

if __name__ == '__main__':
    res = [run(b) for b in (256, 384)]
    for r in res:
        for o in r['results']:
            print(r['precision'], 'D%d' % o['dimension'], '%.12f' % o['enclosure'], o['positive_cells'], o['negative_cells'])
    assert [ (o['lower'], o['upper']) for o in res[0]['results'] ] == [ (o['lower'], o['upper']) for o in res[1]['results'] ]
    json.dump(res, open('heat-upper-bounds.json', 'w'), indent=1)
    print('OK')
