"""Independent D10 origin check. Run with python-flint (tested at 0.8.0).

In the angular-frequency convention Fourier inversion at zero gives
f10(0) = area(S^9)/(2*pi)^10 times the integral of t^9 F(t) for t>0.
Shift the entire real Fourier line for exp(lambda*z^2)*Phi(z) to Im z=1/4.
Theta is analytic in this strip and rapidly decreasing at both ends
(on the left use evenness). Reflection about the imaginary axis gives
Z F(t) = 2 Re integral_0^infty exp(it*z) exp(lambda*z^2)*Phi(z) du,
z=u+i/4. Since |exp(it*z)|=exp(-t/4), absolute convergence allows
integration in t first. Its ninth moment is 9!/(-iz)^10 = -9!/z^10.
With area(S^9)=2*pi^5/4!, this gives the factor below. No Taylor
coefficients, singular real-axis quadrature or dimension walk is used.
"""
from math import factorial
from flint import acb, arb, ctx


def enclose(numerator, denominator, bits):
    ctx.prec = bits
    pi = arb.pi()
    lam = arb(numerator)/denominator
    assert -1 <= lam <= 0
    height = arb(1)/4
    end = 3
    first_omitted = 12

    def integrand(u, analytic):
        z = u + acb(0, height)
        base = pi*(2*z).exp()
        theta = acb(0)
        for n in range(1, first_omitted):
            x = base*n*n
            theta += (-x).exp()*x*(2*x-3)
        return (lam*z*z+z/2).exp()*theta/z**10

    integral = acb.integral(integrand, 0, end, abs_tol=arb(2)**-100,
                            rel_tol=arb(2)**-100).real
    # A=Re X >= 2 exp(2u)n^2; |X|<=2A. Hence the polynomial
    # prefactor times exp(-A/2) is <= 8*(4/e)^2 + 6*(2/e) < 32.
    e = arb(1).exp()
    assert pi*(2*height).cos()>2 and (2*height).cos()>arb(1)/2
    assert 8*(4/e)**2+12/e<32
    omitted = (end*4**10*32*(arb(end)/2+height**2).exp()
               *arb(-first_omitted**2).exp()/(1-1/e))
    # u>=3: exp(2u)n^2 >= 300+2u+n, by its value and derivative
    # at u=3 for n=1 and n^2-1>=n-1. |z|>=1 on this tail.
    assert (arb(2)*end).exp()>300+2*end+1
    far = 32*(height**2-300).exp()/(e-1)  # integral exp(-3u/2) < 1
    integral += arb(0, (omitted+far).upper())
    factor = -arb(4)*factorial(9)/(factorial(4)*2**10)
    value = factor*integral
    print(bits, numerator, denominator, value, flush=True)
    return value


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O.")
    for bits in (192, 256):
        assert enclose(-1, 1024, bits)<0
        assert enclose(-398448, 1000000, bits)<0
        assert enclose(-398449, 1000000, bits)>0
