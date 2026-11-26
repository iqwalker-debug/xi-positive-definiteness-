# Paper III, preprint v1 — Ian Walker

Finite witnesses for failure of positive definiteness in quadratic Dirichlet L-functions. November 25, 2026. Preprint for independent review.

Read Paper-III.pdf. Paper-III.tex is the complete, editable manuscript. The 18 small-prime signs, truncation at n=300, common test points and upper bound for individual unknown terms define the optimization result. All proportions are relative to primes congruent to 3 modulo 4. A row absent from a table is inconclusive.

## Reproduce the manuscript

From the paper-iii directory in a checkout, or the top-level directory of the extracted paper package, run on Linux:

    sh replay.sh

Requirements: Python 3.10 or later with assertions enabled, NumPy, a GNU C++17 compiler with undefined-behavior sanitizer support, cmp and sha256sum. Tested with Python 3.12.14, NumPy 2.3.5 and GCC 14.2. The replay uses temporary disk space for two 65 MiB enclosure files. No network connection is required after dependencies are installed. The checks include archive integrity, three witness tables, grid subset counts, the prime examples 2339 and 20219, and both exhaustive upper-bound calculations. The final test checks every recorded witness against the continuous bounds at its rational test point, using both adjacent intervals for partition boundaries. The Python and C++ upper-bound implementations share a mathematical reduction and partition. A second implementation does not constitute external peer review.

## Outputs to expect

| Result | Count |
|---|---:|
| All possible sign patterns | 262144 |
| Strict majority | 131073 |
| Four explicit points (b = 4, 52, 212, 1100) | 129840 |
| Four arbitrary points, tangent-and-chord upper bound | 129901 |
| Five explicit points | 131854 |
| Original eleven-point grid | 132606 |
| Combined sixteen-point grid | 133315 |
| New-only / original-only | 709 / 1461 |

The Python curvature method visits 2254 boxes; its largest terminal upper bound is 129903. The C++ tangent method with a different tree traversal visits 648429 boxes; its largest terminal upper bound is 129901. This leaves a gap of 61 masks above the explicit four-point construction. The witness-to-enclosure cross-check covers 264460 distinct (mask, denominator) pairs and 668184 individual inclusions. The CSVs record only the first successful denominator per mask in each grid; the original grid's b=10 adds no new masks after b=5.

## Referee entry points

- Sections 1 and 3 give the analytic criterion, arithmetic progression weights and certificate definition; Section 2 proves the Fourier and Fekete implications and identifies the earlier density-one result. Sections 5 and 6 give the continuous bound, including outward rounding and exhaustive coverage. Section 7 explains delayed witnesses.
- In certificate/, witnesses.csv is the original grid, five-witnesses.csv the five-point grid, and combined-witnesses.csv their union. Rows have two integers with no header, mask and denominator b. One bits mean negative Legendre symbols; bit zero corresponds to 2 and bit 17 to 61. The test point is 1 - 1/b.
- From certificate/, python3 lookup.py 2339 reproduces an original-grid witness; the lookup takes primality as a precondition. python3 compare.py reproduces the new prime example and grid comparison. The expected JSON files preserve exact counts, hashes and cumulative results.
- To typeset the manuscript with a standard TeX Live installation, run latexmk -pdf Paper-III.tex. The archive checksum is for the supplied PDF; re-typesetting can change PDF metadata.

Independent expert review and priority assessment for the specific finite certificate are outstanding. This is computer-assisted, AI-assisted work. No Lean formalization is claimed.
