"""Certify the smallest eigenvalue of the ten-observation matrix at lags 8 and 16."""
from fractions import Fraction

from flint import acb, arb, arb_mat, ctx


def theta_terms(k):
    base = arb.pi() * (2*k).exp()
    total = 0
    for n in range(1, 9):
        x = base * n**2
        total += (k/2 - x).exp() * x * (2*x - 3)
    return total


def spatial_integral(t):
    """Enclose the unnormalized cosine transform on the positive frequency line."""
    result = arb(0)
    tolerance = arb(2)**-187
    for q in range(12):
        result += acb.integral(
            lambda k, analytic: theta_terms(k) * (t*k).cos(),
            arb(q)/4, arb(q + 1)/4, abs_tol=tolerance, rel_tol=tolerance,
        ).real

    # Uniform in t since |cos(t k)| <= 1 on the integration line.
    pi = arb.pi()
    theta_tail = 2 * (-81*pi/2).exp() / (1 - (-19*pi/2).exp())
    radial_tail = 16 * (-pi * arb(6).exp()/2).exp()
    return result + arb(0, (theta_tail + radial_tail).abs_upper())


def decimal_ball(text):
    """Outward enclosure of a decimal interpreted as an exact rational."""
    value = Fraction(text)
    return arb(value.numerator) / value.denominator


def shifted_minor(matrix, n, shift):
    return arb_mat([
        [matrix[i][j] - shift * (i == j) for j in range(n)]
        for i in range(n)
    ]).det()


def verify(bounds):
    ctx.prec = 224
    lower = decimal_ball(bounds["lower"])
    upper = decimal_ball(bounds["upper"])
    width = Fraction(bounds["upper"]) - Fraction(bounds["lower"])
    if width != Fraction(1, 10**35):
        raise ValueError("expected consecutive rational shifts of width 1e-35")

    mass = spatial_integral(0)
    if not mass > 0:
        raise ArithmeticError("could not certify positive normalization")
    spatial = [arb(1)] + [spatial_integral(8*i)/mass for i in range(1, 5)]
    delayed = list(map(decimal_ball, ("-3/50", "1/2", "1/2", "0", "-9/25")))
    matrix = []
    for i in range(10):
        row = []
        for j in range(10):
            block = spatial if i//5 == j//5 else delayed
            row.append(block[abs(i % 5 - j % 5)])
        matrix.append(row)

    for n in range(1, 11):
        if not shifted_minor(matrix, n, lower) > 0:
            raise ArithmeticError(f"leading minor {n} at the lower shift failed")
    if not shifted_minor(matrix, 10, upper) < 0:
        raise ArithmeticError("determinant at the upper shift failed")
    print("Ten positive leading minors at the lower shift; negative determinant at the upper.")
    print("PASS minimum_eigenvalue", bounds["lower"], bounds["upper"])
