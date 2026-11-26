#!/usr/bin/env python3
"""Postcomparison additional controls; imports unchanged frozen implementation."""
from flint import arb
from fourier_certificate import enclose, fourier, gaussian_cf, gaussian_tail, templates, xi_cf, xi_tail


for a in (2, 4, 5, 8, 10, 16):
    cap = ((1+xi_cf(2*a))/2).sqrt()
    h1 = enclose(a, templates["single"], xi_cf, xi_tail(a))
    print("a =", a, "three-event cap =", cap, "H1 =", h1)

f10 = xi_cf(10)
candidate = arb(7)/10
print("a=5 three-event determinant =", (1-f10)*(1+f10-2*candidate**2))
print("a=5 excess of 0.7 over H1 =", candidate-enclose(5, templates["single"], xi_cf, xi_tail(5)))
for name,cf,tail in (("xi",xi_cf,xi_tail), ("Gaussian",gaussian_cf,gaussian_tail)):
    # These are q(x)*cos(jx), q=sign(cos(x)+cos(2x)). Its values on [0,pi]
    # change formula at pi/3. The coefficient routine accepts signed outputs.
    for j in (1,2):
        support_point = enclose(8, ([(j,1)],3,1), cf, tail(8))
        print(name, "sum maximizer coordinate", j, "=", support_point)
