#!/usr/bin/env python3
"""Interval certificates by Fourier coefficients in the angular variable.

Usage: python fourier_certificate.py (requires python-flint).
The s=1/2+it normalization is entire and real on real t by conjugation and
the functional equation. All displayed bracketed numbers are Arb enclosures.

For g = |h| on [0,pi], with h(x) = sum_j d_j cos(jx), h >= 0 up to theta
and h <= 0 afterwards. Its complex Fourier coefficients are real:
c_n = (2 int_0^theta - int_0^pi) h(x)cos(nx) dx / pi.
The resulting Fourier series is absolutely convergent (piecewise smooth
first derivative of a continuous function, hence c_n = O(n^-2)).
The expectation against an even characteristic function F(na) therefore
equals c_0 + 2 sum_{n>=1} c_n F(na). In all cases |c_n| <= 2.

For t >= 1 on the critical line, summation by parts gives
zeta(s)=s/(s-1)-s*integral_1^infty {x} x^(-s-1) dx, so
|zeta(s)| <= 1+2|s| <= 7t/2, and |s(s-1)| <= 5t^2/4.
For integer m>4, gamma recurrence and Euler's absolutely integrable
representation at Re(z)=m+1/4 imply |Gamma(1/4+it/2)| <=
Gamma(m+1/4)*(2/t)^m. Thus |F(t)| <= C*t^(3-m), C below.
For n>N, sum n^(3-m) <= N^(4-m)/(m-4). The factor of 4 accounts
for the two symmetric modes and the uniform |c_n| bound.

For the Gaussian, the ratio of successive positive F(na) for n>=N+1
is <= exp(-var*a^2*(2*N+3)/2). A geometric majorant then suffices.
"""
import argparse
from functools import lru_cache
from flint import acb, acb_series, arb, ctx

parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
parser.add_argument("--bits", type=int, default=240)
parser.add_argument("--terms", type=int, default=96)
parser.add_argument("--gamma-shift", type=int, default=40)
args = parser.parse_args()
assert args.bits >= 80 and args.terms >= 1 and args.gamma_shift > 4
ctx.prec = args.bits
ctx.cap = 3
pi = arb.pi()
half = arb(1)/2
quarter = half/2
templates = {
    "single": ([(1, 1)], 2, 1),
    "plus": ([(1, 1), (2, 1)], 3, 1),
    "minus": ([(1, 1), (2, -1)], 3, 2),
}


def xi(s):
    return half*s*(s-1)*(-s*(pi.log()/2)).exp()*(s/2).gamma()*s.zeta()


xi0 = xi(acb(half)).real
assert xi0 > 0


@lru_cache(maxsize=None)
def xi_cf(t):
    if t == 0:
        return arb(1)
    val = xi(acb(half, t))/xi0
    assert 0 in val.imag
    return val.real


xi_series = xi(acb_series([acb(half), acb(0, 1)]))/xi0
assert 0 in xi_series[2].imag
variance = -2*xi_series[2].real
assert variance > 0


def gaussian_cf(t):
    return (-variance*(arb(t)**2)/2).exp()


def sin_integral(n, numerator, denominator):
    if n == 0:
        return pi*numerator/denominator
    return (arb(n*numerator)/denominator).sin_pi()/n


def fourier(n, terms, denominator, numerator):
    result = arb(0)
    for j, weight in terms:
        first = sin_integral(n-j, numerator, denominator)
        second = sin_integral(n+j, numerator, denominator)
        result += weight*((first+second)/pi - (half if n==j else 0))
    return result


def xi_tail(a):
    m = args.gamma_shift
    N = args.terms
    constant = arb(35)/16 * (pi**(-quarter)) * (m+quarter).gamma() * (2**m) / xi0
    return 4*constant*(arb(a)**(3-m))*(arb(N)**(4-m))/(m-4)


def gaussian_tail(a):
    N = args.terms
    return 4*gaussian_cf(a*(N+1))/(1-(-variance*a*a*(2*N+3)/2).exp())


def enclose(a, template, cf, tail):
    coeff = fourier(0, *template)
    for n in range(1, args.terms+1):
        coeff += 2*fourier(n, *template)*cf(a*n)
    return coeff + arb(0, tail.abs_upper())


if __name__ == "__main__":
    print("bits =", args.bits, " terms =", args.terms, " gamma shift =", args.gamma_shift)
    print("xi(1/2) =", xi0)
    print("variance =", variance)
    for a in (8, 5):
        for name, cf, error in (("xi", xi_cf, xi_tail),("Gaussian", gaussian_cf, gaussian_tail)):
            tail = error(a)
            print(f"a={a} distribution={name} uniform bound on omitted terms =", tail)
            for j in range(1, 5):
                print(f"a={a} distribution={name} F({a*j}) =", cf(a*j))
            for fn, template in templates.items():
                value = enclose(a, template, cf, tail)
                print(f"a={a} distribution={name} {fn} =", value)
