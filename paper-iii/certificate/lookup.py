"""Look up a witness for a known prime p > 61, p = 3 mod 4 (primality is an input)."""
import argparse
from fractions import Fraction
from pathlib import Path
from certificate18 import PRIMES, direct_upper_weights

def lookup(p):
    if p <= 61 or p % 4 != 3:
        raise ValueError("Requires a known prime > 61 congruent to 3 modulo 4.")
    mask = 0
    for i, ell in enumerate(PRIMES):
        symbol = pow(ell, (p - 1) // 2, p)
        if symbol not in (1, p - 1):
            raise ValueError("Input fails Euler's criterion for this family.")
        if symbol == p - 1:
            mask |= 1 << i
    with Path(__file__).with_name("witnesses.csv").open() as rows:
        for row in rows:
            m, b = map(int, row.split(","))
            if m == mask:
                terms, error = direct_upper_weights(b)
                upper = error + sum(-weight if (key & mask).bit_count() % 2 else weight
                                    for weight, key in terms)
                if upper >= 0:
                    raise ArithmeticError("Witness failed direct replay.")
                return f"p={p} mask={mask} b={b} H_p(1-1/b) <= {Fraction(upper, 1 << 80)}"
    return f"p={p} mask={mask}: unresolved by this certificate."

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("p", type=int)
    print(lookup(parser.parse_args().p))
