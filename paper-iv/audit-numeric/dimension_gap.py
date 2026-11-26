"""Enclose H8(5) - H9(5) directly through the negative angular lobes."""
from functools import lru_cache

from flint import arb, ctx

RADIAL_CELLS = 6144
ANGULAR_CELLS = 3072
SEPARATION = 5


def angular(dimension, z):
    """Normalized spherical Fourier kernel, evaluated here only for z > 0."""
    order = arb(dimension)/2 - 1
    return (order + 1).gamma() * (2/z)**order * z.bessel_j(order)


@lru_cache(maxsize=None)
def taylor_data(dimension, index):
    center = arb(index) / 1000
    value = angular(dimension, center)
    derivative = -center * angular(dimension + 2, center) / dimension
    return center, value, derivative


def angular_range(dimension, z):
    # The float chooses only a nearby expansion center, not an interval endpoint.
    index = round(1000 * float(z.mid()))
    center, value, derivative = taylor_data(dimension, index)
    offset = z - center
    # |Omega''(s)| <= E[U_1^2] = 1/d everywhere.
    radius = (abs(offset).upper()**2 / (2*dimension)).upper()
    return value + derivative * offset + arb(0, radius)


def derivative_polynomials():
    """Polynomials left after differentiating exp(r/2-X) X(2X-3)."""
    polynomials = [[arb(0), arb(-3), arb(2)]]
    for _ in range(4):
        prev = polynomials[-1]
        nxt = [arb(0)] * (len(prev) + 1)
        for j, coefficient in enumerate(prev):
            nxt[j] += (arb(1)/2 + 2*j) * coefficient
            nxt[j+1] -= 2 * coefficient
        polynomials.append(nxt)
    return polynomials


def evaluate(coefficients, x):
    result = arb(0)
    for coefficient in reversed(coefficients):
        result = result*x + coefficient
    return result


def radius_density(r, polynomials, pi, area, normalizer):
    """Outward enclosure of the nine-dimensional probability density in radius."""
    coefficients = [arb(0)] * len(polynomials[4])
    for order, factor in ((4, r**3), (3, -6*r**2), (2, 15*r), (1, -15)):
        for j, value in enumerate(polynomials[order]):
            coefficients[j] += factor * value
    x = pi * (2*r).exp()
    first = (-x).exp() * evaluate(coefficients, x)
    # For n>=2, enclose P(X)/X^6 on 0 <= 1/X <= 1/(4x).
    scaled = evaluate(coefficients[::-1], arb(0).union(1/(4*x)))
    tail = abs(scaled) * (4*x)**6 * (-4*x).exp() / (1 - (arb(3)/2)**12 * (-5*x).exp())
    prefactor = area * r * (r/2).exp() / ((2*pi)**4 * normalizer)
    return prefactor * (first + arb(0, tail.upper()))


def tail_mass(r_max, pi, normalizer):
    # The interval [.94,.95] gives a lower bound on P(|U_1|>.94) in nine dimensions.
    angular_probability = (
        arb(1)/100 * 2 * (arb(9)/2).gamma() / (pi.sqrt() * arb(4).gamma())
        * (1 - (arb(95)/100)**2)**3
    )
    x = pi * (2*r_max * arb(94)/100).exp()
    # P(R>r_max) P(|U_1|>.94) <= P(|K_1|>.94 r_max).
    return (x**2 + 2*x + 2) * (-x).exp() / (1 - 16 * (-3*x).exp()) / (normalizer/2) / angular_probability


def verify(bounds):
    ctx.prec = 180
    pi = arb.pi()
    half = arb(1)/2
    xi_zero = half * (half - 1) * pi**(-half/2) * (half/2).gamma() * half.zeta() / 2
    normalizer = xi_zero/2  # integral of the unfolded, even theta density
    area = 2 * pi**(arb(9)/2) / (arb(9)/2).gamma()
    beta = arb(4).gamma() * half.gamma() / (arb(9)/2).gamma()
    polynomials = derivative_polynomials()
    r_min, r_max = arb(126)/100, arb(160)/100
    theta_max = arb(7)/10
    positive_to = arb(63)/10

    # Cos(z U1)>0 for 0<=z<=1. Certify positivity through 6.3 using |Omega'|<=1.
    for i in range(5300):
        center = arb(2001 + 2*i)/2000
        if not angular(8, center) > 1/arb(2000):
            raise ArithmeticError("failed positivity on the low-frequency interval")
    if not (theta_max < pi/2 and SEPARATION*r_max*theta_max.cos() < positive_to):
        raise ArithmeticError("excluded angles are outside the positive-kernel range")
    # R<=1.26 gives zero deficit, and theta>=0.7 contributes no negative 8D lobe.
    tail = tail_mass(r_max, pi, normalizer)
    if not tail < arb("1e-17"):
        raise ArithmeticError("radial tail too large")

    angle_step = theta_max / ANGULAR_CELLS
    angles = []
    for j in range(ANGULAR_CELLS):
        angle = (angle_step*j).union(angle_step*(j+1))
        cosine = angle.cos()
        angles.append((cosine, 2 * cosine**7 / beta))

    total = arb(0)
    zero = arb(0)
    r_step = (r_max - r_min) / RADIAL_CELLS
    for i in range(RADIAL_CELLS):
        r = (r_min + i*r_step).union(r_min + (i+1)*r_step)
        z_max = SEPARATION * r
        negative_part = arb(0)
        for cosine, weight in angles:
            z = z_max * cosine
            if z.upper() <= positive_to:
                continue
            negative_part += (-angular_range(8, z)).max(zero) * weight
        negative_part *= angle_step
        projected_neg = (-angular_range(9, z_max)).max(zero)
        deficit = (2 * (negative_part - projected_neg)).max(zero)
        density = radius_density(r, polynomials, pi, area, normalizer)
        if not density > 0:
            raise ArithmeticError(f"could not certify positivity in radius cell {i}")
        total += r_step * density * deficit
    total += zero.union(tail.upper())

    if not arb(bounds["lower"]) < total or not total < arb(bounds["upper"]):
        raise ArithmeticError(f"dimension gap exceeds the declared enclosure: {total.lower()}, {total.upper()}")
    print("Radial tail mass <=", tail.upper())
    print("Calculated gap endpoints:", total.lower(), total.upper())
    print("PASS dimension_gap", bounds["lower"], bounds["upper"])
