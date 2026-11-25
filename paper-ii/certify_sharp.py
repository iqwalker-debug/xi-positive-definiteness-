"""Sharpness certificate for the odd-dimensional heat endpoints, odd d = 5..27 (python-flint 0.9.0).

Claim certified, for m = 2..13 and lambda_m the smallest real root of P_m (enclosed in
heat-upper-bounds.json):   Q_m(x; lambda_m) > 0 for every x > 0,
where Q_m(x; lam) = (-1)^m sum_k C(m,k) lam^(m-k) H^(k)(x),  H(x) = Phi(sqrt x).

Three regions in x = r^2:
  A. 0 <= x <= 1/16 : dQ_m/dx > 0 for every lam in the enclosure. Since Q_m(0; lambda_m) = 0, Q_m > 0 on (0, 1/16].
  B. 1/16 <= x <= 1/4: Q_m > 0 for every lam in the enclosure.
  C. r >= 1/2      : every theta summand of Q_m is positive (exact polynomial coefficient signs).
A and B use the Taylor series of H at 0 with a Cauchy remainder: H is analytic on |x| < (pi/4)^2,
|H| <= M on |x| <= rho = 3/5, so |a_k| <= M rho^-k.
"""
if not __debug__:
    raise SystemExit("Verification requires Python assertions. Remove -O or PYTHONOPTIMIZE.")

from fractions import Fraction as F
import json, math
from flint import arb, acb, ctx
import sympy as sp

K = 120                      # Taylor degree in x
RHO = F(3, 5)
DELTA_A, DELTA_B = F(1, 16), F(1, 4)

def ball(x):
    x = F(x); return arb(x.numerator) / x.denominator

def theta_polys(kmax):
    polys = [[F(0), F(-3), F(2)]]
    for _ in range(kmax):
        old = polys[-1]
        polys.append([(F(1,2)+2*j)*(old[j] if j < len(old) else 0) - (2*old[j-1] if j else 0)
                      for j in range(len(old)+1)])
    return polys

def taylor_coeffs(polys):
    """a_k = Phi^(2k)(0)/(2k)!, 0 <= k <= K, as balls with a rigorous series tail."""
    pi = arb.pi(); N = 60; XN = pi*N*N
    a = []; f = arb(1)
    for k in range(K+1):
        j = 2*k
        if k: f = f*(j-1)*j
        assert XN > 2*(j+2)                     # X^(j+2) exp(-X/2) decreasing beyond this
        C = sum(abs(c) for c in polys[j])
        tail = ball(C) * XN**(j+2) * (-XN/2).exp() * 2 * (-XN/2).exp()
        s = arb(0, tail.upper())
        for n in range(1, N):
            x = pi*n*n; p = arb(0)
            for c in reversed(polys[j]): p = p*x + ball(c)
            s += (-x).exp()*p
        a.append(s/f)
    return a

def sup_bound():
    """M >= sup |H(x)| on |x| <= RHO. There |Re r|, |Im r| <= sqrt(RHO) =: t < pi/4."""
    pi = arb.pi(); t = ball(RHO).sqrt()
    assert 2*t < pi/2                           # cos(2 Im r) >= cos(2t) > 0
    absX = pi*(2*t).exp()                       # |X_n| <= absX n^2
    reX = pi*(-2*t).exp()*(2*t).cos()           # Re X_n >= reX n^2
    assert reX > ball(F(1, 80))
    M = arb(0)
    for n in range(1, 2001):
        M += absX*n*n*(2*absX*n*n+3)*(-reX*n*n).exp()
    # n > 2000: absX n^2 (2 absX n^2 + 3) <= 1000 n^4 <= exp(n^2/200), and Re X_n >= n^2/80,
    # so each term is <= exp(-3 n^2/400)
    assert absX < 20 and 1000*arb(2000)**4 < (arb(2000)**2/200).exp()
    M += 2*(-3*arb(2001)**2/400).exp()
    return M*(t/2).exp()

def run(bits):
    ctx.prec = bits
    polys = theta_polys(2*K)
    a = taylor_coeffs(polys)
    M = sup_bound()
    bounds = {o['m']: (F(o['lower']), F(o['upper'])) for o in json.load(open('heat-upper-bounds.json'))[0]['results']}
    fact = [arb(1)]
    for i in range(1, K+2): fact.append(fact[-1]*i)
    rho = ball(RHO)

    def H(j, x, delta):
        """Enclosure of H^(j) on the ball x, x within [0, delta]."""
        p = arb(0)
        for k in range(K, j-1, -1):
            p = p*x + a[k]*fact[k]/fact[k-j]
        d = ball(delta)
        assert ((arb(K+2)/(K+1))**j)*d/rho < ball(F(1,2))
        rem = 2*M*d**(-j)*arb(K+1)**j*(d/rho)**(K+1)
        return p + arb(0, rem.upper())

    def binom(m, k): return math.comb(m, k)

    # region C polynomials (exact in r, X; lam kept symbolic)
    r, X, z, u, lam = sp.symbols('r X z u lam')
    w = [2*X**2 - 3*X]
    max_m = 13
    for k in range(max_m):
        wk = w[-1]
        w.append(sp.expand(r*(2*X-sp.Rational(1,2))*wk - 2*r*X*sp.diff(wk, X) - r*sp.diff(wk, r)
                           + 2*k*wk - 2*lam*r**2*wk))
    Rr = sp.Rational(1, 2); c = sp.Rational(8539, 1000)
    assert arb.pi()*arb(1).exp() > ball(F(8539, 1000))      # pi e^(2R) >= c, and e^(2z) >= 1+2z+2z^2

    out = []
    for m in range(2, max_m + 1):
        lo, hi = bounds[m]; L = ball(lo).union(ball(hi)); sgn = 1 if m % 2 == 0 else -1
        def Q(x, delta, shift):
            return sgn*sum(binom(m, k)*L**(m-k)*H(k+shift, x, delta) for k in range(m+1))
        cells = {'A': 0, 'B': 0}
        def cover(l, rr, key, delta, shift, depth=0):
            v = Q(ball(l).union(ball(rr)), delta, shift)
            if v > 0: cells[key] += 1; return
            if depth > 40: raise ValueError((m, key, str(l), str(rr), str(v)))
            mid = (l+rr)/2
            cover(l, mid, key, delta, shift, depth+1); cover(mid, rr, key, delta, shift, depth+1)
        cover(F(0), DELTA_A, 'A', DELTA_B, 1)        # derivative positive near the origin
        cover(DELTA_A, DELTA_B, 'B', DELTA_B, 0)     # value positive in the middle
        e = sp.expand(w[m].subs({r: Rr+z, X: c*(1+2*z+2*z**2)+u}))
        P = sp.Poly(e, z, u, domain=sp.QQ[lam])
        assert P.coeff_monomial((0, 0)) != 0, (m, "missing constant term")
        ncoef = 0
        for coeff in P.coeffs():
            pl = sp.Poly(coeff, lam)
            v = arb(0)
            for cc in pl.all_coeffs(): v = v*L + ball(F(int(cc.p), int(cc.q)))
            assert v > 0, (m, 'tail coefficient', str(v))
            ncoef += 1
        out.append(dict(dimension=2*m+1, lambda_lower=str(lo), lambda_upper=str(hi),
                        cells_A=cells['A'], cells_B=cells['B'], tail_coefficients=ncoef))
    return dict(precision=bits, taylor_degree=K, sup_bound=str(M), results=out)

if __name__ == '__main__':
    res = [run(b) for b in (512, 768)]
    for rr in res:
        for o in rr['results']:
            print(rr['precision'], 'D%d' % o['dimension'], 'A', o['cells_A'], 'B', o['cells_B'], 'tail', o['tail_coefficients'])
    with open('heat-sharpness.json', 'w') as f: json.dump(res, f, indent=1)
    print('OK')
