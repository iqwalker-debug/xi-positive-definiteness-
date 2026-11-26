"""Replay the concrete bounds used by XiHeatConsequences.lean, with Arb."""
import argparse
from math import factorial

from flint import acb, acb_series, arb, ctx
from certify_finite import histogram


def phi(r):
    """Enclose Phi at the three nonnegative radii used in the midpoint test."""
    total = arb(0)
    for n in range(1, 17):
        x = arb.pi()*n*n*(2*r).exp()
        total += (r/2-x).exp()*x*(2*x-3)
    # X² exp(-X/2) <= 16/e². Bound the tail from n=17 by a geometric series.
    tail = 12*(r/2-arb.pi()*17**2/2).exp()
    return total + arb(0, tail.upper())


def xi_jet(t):
    s = acb_series([acb(arb(1)/2, t), acb(0, 1)], prec=ctx.cap)
    return s*(s-1)/2 * (s/2).gamma() * (-s/2*arb.pi().log()).exp() * s.zeta()


def certify(bits):
    ctx.prec = bits
    degree = 12
    ctx.cap = 2*degree + 1
    weights, norm = histogram()
    xi0 = xi_jet(0)[0].real
    if not xi0/2 > arb(1)/5:
        raise ValueError("Lower bound on the spectral mass failed")
    coefficients = [arb(0) for _ in range(degree+1)]
    for k, weight in enumerate(weights):
        if weight:
            jet = xi_jet(7*arb(k).sqrt())
            for j in range(degree+1):
                coefficients[j] += arb(weight)/norm * jet[2*j].real
    for j in range(degree+1):
        coefficients[j] *= (-1)**j * factorial(2*j)/(arb(factorial(j))*xi0)

    if not (coefficients[0] < -arb(1259)/100000 and
            -arb(1513)/100 < coefficients[1] < -arb(1511)/100 and
            all(abs(a) < 5 for a in coefficients[2:])):
        raise ValueError("Heat Taylor coefficient enclosure failed")
    moment_factor = arb(sum(weights))/norm * 30 * (arb.pi()/3).sqrt()
    if not moment_factor < 10**11:
        raise ValueError("Gaussian-moment prefactor is too large")

    left, mid, right = (phi(r) for r in [arb(0), (arb(1)/2).sqrt(), arb(1)])
    if not (0 < left < arb(1)/2 and mid > arb(1)/1000 and
            0 < right < arb(1)/5000000):
        raise ValueError("Theta midpoint enclosures failed")
    print(f"{bits} bits: 13 coefficient boxes, moment prefactor and 3 theta bounds passed")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--bits", choices=[192, 256], type=int, required=True)
    certify(parser.parse_args().bits)
