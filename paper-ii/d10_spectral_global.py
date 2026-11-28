"""D10 spectral shape on the entire candidate endpoint bracket. Run beside the other
Paper II scripts. See the projection argument in d10-spectral-global.md.
"""
from fractions import Fraction
from math import prod

import sympy as sp
from flint import arb, ctx
from certify_sharp import K, RHO, ball, sup_bound, taylor_coeffs, theta_polys
from d10_origin_contour import enclose


def check_global(bits):
    ctx.prec = bits
    lam = Fraction(-398449, 1000000)
    upper = Fraction(-398448, 1000000)
    L = ball(lam).union(ball(upper))
    # g(x)=exp(lambda*x)*Phi(sqrt(x)). Enclose its Taylor coefficients.
    theta = taylor_coeffs(theta_polys(2*K))
    heats = [arb(1)]
    for j in range(1,K+1):
        heats.append(heats[-1]*L/j)
    g = [sum(theta[i]*heats[k-i] for i in range(k+1)) for k in range(K+1)]
    rho = ball(RHO)
    M = sup_bound()*(abs(L)*rho).exp()
    D = arb(1)/4

    def certify(order, left, right):
        coeff = [-g[k]*prod(range(k-order+1,k+1)) for k in range(order,K+1)]
        # Cauchy tail for the differentiated Taylor series on [0,1/4].
        ratio = (arb(K+2)/(K+1))**order*D/rho
        assert ratio < 1
        remainder = M*D**(-order)*arb(K+1)**order*(D/rho)**(K+1)/(1-ratio)
        def cover(a,b,depth):
            x = ball(a).union(ball(b))
            p = arb(0)
            for v in reversed(coeff):
                p=p*x+v
            if p > remainder:
                return 1
            if depth>=30:
                raise ArithmeticError((order,a,b,p,remainder))
            mid=(a+b)/2
            return cover(a,mid,depth+1)+cover(mid,b,depth+1)
        return cover(left,right,0)

    assert -g[5]<0
    derivative_cells=certify(6,Fraction(0),Fraction(1,16))
    positive_cells=certify(5,Fraction(1,16),Fraction(1,4))

    # For r>=1/2 certify each theta summand individually by the Paper II
    # recurrence for (-d/dx-lambda)^5 H, x=r^2, with a positive prefactor.
    r,X,z,u,h=sp.symbols('r X z u h')
    w=2*X**2-3*X
    for k in range(5):
        w=sp.expand(r*(2*X-sp.Rational(1,2))*w-2*r*X*sp.diff(w,X)
                    -r*sp.diff(w,r)+2*k*w-2*h*r*r*w)
    c=sp.Rational(8539,1000)
    assert arb.pi()*arb(1).exp()>ball(Fraction(8539,1000))
    tail=sp.Poly(w.subs({r:z+sp.Rational(1,2),X:c*(1+2*z+2*z*z)+u}),z,u)
    assert tail.coeff_monomial(1) != 0
    for coeff in tail.coeffs():
        v=arb(0)
        for a in sp.Poly(coeff,h).all_coeffs():
            v=v*L+ball(Fraction(int(a.p),int(a.q)))
        assert v>0
    assert enclose(lam.numerator,lam.denominator,bits)>0
    assert enclose(upper.numerator,upper.denominator,bits)<0
    assert enclose(-398448207016,10**12,bits)>0
    assert enclose(-398448207015,10**12,bits)<0
    print(bits, "PASS", derivative_cells, positive_cells, len(tail.coeffs()), flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O.')
    for precision in (512,768):
        check_global(precision)
