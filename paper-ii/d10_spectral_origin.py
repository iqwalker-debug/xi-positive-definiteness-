"""Arb enclosure of the sign of f_10(0) at heat parameter -1/1024.

Angular frequency convention: let g(x)=exp(lambda*x)*Phi(sqrt(x)), Z>0.
Projection from 11 dimensions gives pi^5*Z*f_10(0)=-int g^(5)(x)/sqrt(x) dx.
Subtract the degree-4 Taylor polynomial T(x) and integrate by parts five times:
pi^5*Z*f_10(0) = -2*(1/2)_5 * J, J=int (g(r^2)-T(r^2))/r^10 dr.
All integrals are on the positive half-line.
"""
from math import factorial
from flint import acb, arb, ctx

DEGREE = 28

def horner(coeff, x):
    y = 0
    for v in reversed(coeff):
        y = y*x + v
    return y

def coefficients(lam, pi):
    # k-th derivative of Phi at zero before division by k!.
    poly = [arb(0), arb(-3), arb(2)]
    a = []
    for k in range(2*DEGREE + 1):
        if k % 2 == 0:
            start = pi*24**2
            # exp(-X/2)*X^(k+2) decreases from start onwards.
            assert start > 2*(k+2)
            # The other half exponential sums to <= 2 exp(-start/2).
            tail = 2*sum(map(abs, poly))*start**(k+2)*(-start).exp()
            val = arb(0, tail.upper())
            for n in range(1, 24):
                x = pi*n*n
                val += (-x).exp()*horner(poly,x)
            a.append(val/factorial(k))
        poly = [((arb(1)/2+2*j)*v - (2*poly[j-1] if j else 0))
                for j,v in enumerate(poly+[arb(0)])]
    return [sum(a[k]*lam**(j-k)/factorial(j-k) for k in range(j+1))
            for j in range(DEGREE+1)]

def run(bits, numerator, denominator):
    ctx.prec = bits
    pi = arb.pi()
    lam = arb(numerator)/denominator
    assert -1 <= lam <= 0
    b = arb(1)/4
    c = coefficients(lam, pi)
    # For |x|=1/4, |r|=1/2: |X_n|<9n^2 and Re(X_n)>n^2/2.
    # n^4 exp(-n^2/4)<=64/e^2<9 and sum exp(-n^2/4)<=1/(exp(1/4)-1).
    assert pi*arb(1).exp()<9 and pi/arb(1).exp()*arb(1).cos()>arb(1)/2
    M = 9*21*9*(arb(1)/4 + abs(lam)/4).exp()/((arb(1)/4).exp()-1)
    near = sum(c[j]*b**(2*j-9)/(2*j-9) for j in range(5, DEGREE+1))
    rem = M*4**(DEGREE+1)*b**(2*DEGREE-7)/((2*DEGREE-7)*(1-4*b*b))
    near += arb(0, rem.upper())

    def integrand(r, analytic):
        r2 = r*r
        base = pi*(2*r).exp()
        phi = acb(0)
        for n in range(1, 10):
            x = base*n*n
            phi += (r/2-x).exp()*x*(2*x-3)
        return ((lam*r2).exp()*phi-horner(c[:5], r2))/r**10

    mid = acb.integral(integrand, b, 2, abs_tol=1e-20).real
    # On [b,2], 2X^2 exp(-X/2)<=16 and X/2>=n^2.
    # n>=10: sum exp(-n^2)<= exp(-100)/(1-exp(-1)).
    mid_err = 2*4**10*16*arb(1).exp()*arb(-100).exp()/(1-arb(-1).exp())
    mid += arb(0,mid_err.upper())
    far = -sum(c[j]*arb(2)**(2*j-9)/(9-2*j) for j in range(5))
    # r>=2: X/4 >= 3r/2, X/4 >= 40+n as pi*exp(4)/4>41.
    # Thus 0<=exp(lam*r^2)*Phi(r)/r^10 <=16*exp(-r-40)/(e-1).
    assert pi*arb(4).exp()/4>41
    far += arb(0,(16*arb(-42).exp()/(arb(1).exp()-1)).upper())
    scaled = -2*(arb(945)/32)*(near+mid+far)
    print(bits, f"lambda={numerator}/{denominator}", "pi^5 Z f10(0) =", scaled, flush=True)
    return scaled

if __name__ == "__main__":
    import sys
    if not __debug__:
        sys.exit("Run without -O for bound checks.")
    for bits in (192, 256):
        assert run(bits, -1, 1024) < 0
        assert run(bits, -398448, 1000000) < 0
        assert run(bits, -398449, 1000000) > 0
