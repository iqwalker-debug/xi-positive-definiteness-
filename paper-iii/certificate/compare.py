"""Replay the original grid, compare both CSVs and verify the additional example."""
import csv
from fractions import Fraction
from math import isqrt
from pathlib import Path
import certificate18 as cert

def load_table(name):
    with Path(__file__).with_name(name).open(newline="") as rows:
        return {int(m): int(b) for m, b in csv.reader(rows)}

if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Python assertions must be enabled.")
    original, _ = cert.certify()
    five = load_table("five-witnesses.csv")
    combined = load_table("combined-witnesses.csv")
    assert original.keys() | five.keys() == combined.keys()
    assert len(original.keys() - five.keys()) == 1461
    assert len(five.keys() - original.keys()) == 709
    print("Original only: 1461. Five-point only: 709. Combined:", len(combined))
    p = 20219
    assert p % 4 == 3 and all(p % d for d in range(2, isqrt(p) + 1))
    m = sum(1 << i for i, q in enumerate(cert.PRIMES) if pow(q, (p-1)//2, p) == p-1)
    assert m not in original and five[m] == 1438
    terms, error = cert.direct_upper_weights(five[m])
    signed = sum(-weight if (m & key).bit_count() % 2 else weight for weight, key in terms)
    upper = Fraction(signed + error, 1 << 80)
    assert upper == Fraction(-2865299997018384087109295,1208925819614629174706176)
    print(f"p={p}, mask={m}, b={five[m]}, H upper bound={upper}")
