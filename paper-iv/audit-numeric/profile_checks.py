"""Reconstruct the printed fourth derivatives and three-dimensional asymptotic."""
from decimal import Decimal

from flint import acb, acb_series, arb, ctx


def xi(s, pi):
    return s * (s - 1) / 2 * (-s * pi.log() / 2).exp() * (s / 2).gamma() * s.zeta()


def verify_rounded(value, reported, name):
    exponent = Decimal(reported).as_tuple().exponent
    half_unit = arb(10)**exponent / 2
    if not abs(value - arb(reported)) < half_unit:
        raise ArithmeticError(f"{name} falls outside the rounding cell for {reported}")
    print(f"PASS {name} {reported}")


def verify(fourth_derivatives, asymptotic):
    ctx.prec = 192
    ctx.cap = 5
    half = arb(1) / 2
    pi = arb.pi()
    xi_zero = xi(half, pi)
    argument = acb_series([acb(half), acb(0, 1)], prec=5)
    series = xi(argument, pi) / xi_zero
    variance = -2 * series[2].real
    xi_fourth = 24 * series[4].real
    if 0 not in series[2].imag or 0 not in series[4].imag or not variance > 0:
        raise ArithmeticError("invalid normalized Xi expansion near zero")
    verify_rounded(xi_fourth, fourth_derivatives["xi"], "xi_fourth_derivative")
    verify_rounded(3 * variance**2, fourth_derivatives["gaussian"], "gaussian_fourth_derivative")

    # p(0+) is twice the sum of the unnormalized theta terms at zero divided by Z.
    normalizer = xi_zero / 2
    density_sum = arb(0)
    for n in range(1, 9):
        x = pi * n**2
        density_sum += x * (2*x - 3) * (-x).exp()
    first_omitted_x = 81 * pi
    first_majorant = 2 * first_omitted_x**2 * (-first_omitted_x).exp()
    ratio = (arb(10) / 9)**4 * (-19 * pi).exp()
    density_sum += arb(0).union((first_majorant / (1 - ratio)).upper())
    verify_rounded(4 * density_sum / (pi * normalizer), asymptotic, "three_dimensional_asymptotic")
