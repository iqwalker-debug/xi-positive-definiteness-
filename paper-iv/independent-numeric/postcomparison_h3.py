#!/usr/bin/env python3
"""Alternative direct H3 computation by Taylor polynomial integration.

Requires python-flint. No numerical quadrature library or external data.

For p=w/Z, an absolute line-frequency density, the three-dimensional
radial probability law has density -r p'(r). Hence
  H3(a)= integral_0^infinity |sin(ar)| (-w'(r)) dr / (a Z).
The program evaluates this positive-density form, taking w from the
theta-series definition and differentiating its terms algebraically.
Approximation retains r in [0,2], n<=4 and splits at the exact sine zeros.
A degree-nine Taylor polynomial on each cell is integrated exactly. The
order-ten coefficient evaluated on the entire cell bounds its remainder.
"""
from flint import arb, arb_series, ctx

ctx.prec = 150
order = 10
ctx.cap = order + 1
pi = arb.pi()
cutoff = arb(2)
terms = 4
subdivisions_per_unit = 64


def exponentials(r):
    Xbase = pi*(2*r).exp()
    for n in range(1, terms+1):
        X = (n*n)*Xbase
        yield X, (r/2-X).exp()


def weight(r):
    return sum(ex*X*(2*X-3) for X, ex in exponentials(r))


def negative_weight_derivative(r):
    return sum(ex*X*(4*X**2-15*X+arb(15)/2) for X, ex in exponentials(r))


def integrate(f, left, right):
    count = max(1, int(float((right-left)*subdivisions_per_unit)) + 1)
    h = (right-left)/(2*count)
    total = arb(0)
    for i in range(count):
        c = left+(2*i+1)*h
        center = f(arb_series([c,1]))
        cell = f(arb_series([c+arb(0,h.abs_upper()),1]))
        total += sum(2*center[j]*h**(j+1)/(j+1) for j in range(0,order,2))
        error = 2*abs(cell[order])*h**(order+1)/(order+1)
        total += arb(0,error.abs_upper())
    return total


# Tail bounds. Write b=pi*n^2 and X=b*exp(2r). With dr=dX/(2X),
# int_{r0}^infty w_n dr <= b^(-1/4) int_L^infty X^2 exp(-X) dX
# <= (L^2+2L+2) exp(-L) <= 5 exp(-L/2) when L=b exp(2r0)>=25*pi.
# Here X^(5/4) <= X^2, b>1, and L^2 <= exp(L/2) for L>=25*pi.
# Every omitted portion falls into this range. For the derivative integral
# -w'_n>=0 there, so its absolute mass is w_n(r0) <= 2 exp(r0/2-L/2).
# For n>=5, consecutive exp(-pi*n^2/2) have ratio <= exp(-11*pi/2).
series = (-25*pi/2).exp()/(1-(-11*pi/2).exp())
large_r = (-pi*(2*cutoff).exp()/2).exp()
weight_tail = 5*(series+terms*large_r)
derivative_tail = 2*(series+terms*(cutoff/2).exp()*large_r)

Z = integrate(weight, arb(0), cutoff) + arb(0,weight_tail.abs_upper())
assert Z > 0
print("Z =", Z)
print("tail bound for Z =", weight_tail, "; for derivative integral =", derivative_tail)
for a in (2,4,5,8,10):
    breaks = [arb(0)]
    index = 1
    while pi*index/a < cutoff:
        breaks.append(pi*index/a)
        index += 1
    assert pi*index/a > cutoff
    breaks.append(cutoff)
    numerator = arb(0)
    for j,(left,right) in enumerate(zip(breaks,breaks[1:])):
        sign = (-1)**j
        numerator += integrate(lambda r: sign*(a*r).sin()*negative_weight_derivative(r), left, right)
    numerator += arb(0,derivative_tail.abs_upper())
    result = numerator/(a*Z)
    print("a =", a, "H3 =", result)
