"""Certify the spectra of K+J and K-J using similarity-transformed Gershgorin disks.

Python 3, numpy and python-flint. The LAPACK eigenvectors merely propose an
integer change of basis. Every assertion about the spectrum uses Arb balls.
"""
from fractions import Fraction
import numpy as np
import flint
from flint import acb, arb, arb_mat, ctx

ctx.prec = 192


def xi(t):
    s = acb(arb(1) / 2, t)
    half = s / 2
    value = s * (s - 1) / 2 * (-half * arb.pi().log()).exp() * half.gamma() * s.zeta()
    assert value.imag.contains(0)
    return value.real


def number(value):
    return arb(value.numerator) / value.denominator


def certify(label, matrix):
    n = matrix.nrows()
    trial = np.array([[float(matrix[i,j].mid()) for j in range(n)] for i in range(n)])
    _, vectors = np.linalg.eigh(trial)
    basis = arb_mat([[int(round(float(vectors[i,j]) * 10**12)) for j in range(n)] for i in range(n)])
    transformed = basis.inv() * matrix * basis
    intervals = []
    for i in range(n):
        radius = sum(abs(transformed[i,j]) for j in range(n) if i != j)
        intervals.append(((transformed[i,i] - radius).lower(), (transformed[i,i] + radius).upper()))
    assert all(intervals[i][1] < intervals[i+1][0] for i in range(n-1))
    assert all(left > arb(1)/50 for left, _ in intervals)
    print(label)
    for left, right in intervals:
        print(f'  [{left.str(20)}, {right.str(20)}]')
    return intervals


def main():
    print(f'python-flint {flint.__version__}, {ctx.prec} bits')
    normalizer = xi(0)
    entries = [xi(8*d) / normalizer for d in range(5)]
    print('First row of K')
    for d, value in enumerate(entries):
        print(f'  {d}: {value.str(42)}')
    spatial = arb_mat([[entries[abs(i-j)] for j in range(5)] for i in range(5)])
    lag_row = [number(Fraction(q)) for q in ('-3/50', '1/2', '1/2', '0', '-9/25')]
    lag = arb_mat([[lag_row[abs(i-j)] for j in range(5)] for i in range(5)])
    plus = certify('K+J', spatial + lag)
    minus = certify('K-J', spatial - lag)
    assert plus[0][1] < minus[0][0]
    print('The full matrix has its smallest eigenvalue in the first K+J interval.')
    print('All ten eigenvalues are strictly greater than 1/50.')


if __name__ == '__main__':
    main()
