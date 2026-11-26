# Positive-Definiteness Endpoints of Heat-Deformed Riemann Xi Kernels

[Paper II](Paper-II.pdf) by Ian Walker is a working draft awaiting human review. Theorem 5 gives exact endpoints for odd dimensions 3 through 41. The next odd-dimensional case in Conjecture 6 is 43. Dimensions 29 through 41 rest on the two extension certificates below and have had no review. The paper gives bounds on even-dimensional endpoints.

## Reproduce the numerical certificates

From this directory, use Python 3.12 with assertions enabled.

```sh
python -m pip install -r requirements.txt
python certify_bounds.py
python certify_sharp.py
python check_d3.py
python check_export.py
git diff --exit-code -- heat-upper-bounds.json heat-sharpness.json
python integer/upper.py
python integer/sharp.py
python certify_bounds_induction.py
python certify_sharp.py --bounds heat-upper-bounds-extended.json --max-m 20 --output heat-sharpness-extended.json
git diff --exit-code -- heat-upper-bounds-extended.json heat-sharpness-extended.json
```

The last sharpness command takes about 25 minutes.

| Certificate | Coverage and arithmetic |
|---|---|
| `certify_bounds.py` | Thirteen root brackets at 256 and 384 bits in Arb. Each `derivative_upper_on_bracket` string is the exact dyadic upper endpoint expressed as a rational numerator/denominator. |
| `certify_sharp.py` | Three-region sharpness checks for every odd dimension from 5 through 27, at 512 and 768 bits in Arb. |
| `certify_bounds_induction.py` | Root brackets for every odd dimension from 3 through 41 at 512 and 768 bits in Arb, using point evaluations and the identity P'_m = -P_(m-1). The first thirteen brackets must equal those of `certify_bounds.py`, whose interval cover stops deciding signs at dimension 31. |
| `certify_sharp.py --max-m 20` | The same three-region sharpness checks for every odd dimension from 5 through 41, on the induction brackets. |
| `check_d3.py` | Independent cross-check of the dimension-three inequality at 128 and 192 bits. |
| [Integer verifier](integer/README.md) | A second implementation checks the same brackets and sharpness range using directed integer arithmetic and separate Taylor coefficient calculations. |

The integer verifier and the Lean modules cover dimensions through 27 only. The Paper II GitHub Actions workflow reruns Arb, checks all 26 exported bounds at 768 bits, replays the integer verifier, and compares the regenerated bounds and sharpness files byte for byte. The logs report both precisions and every dimension. A second job replays the two extension certificates and compares their files byte for byte.

## Reproduce the Lean checks

With the Lean toolchain manager installed, run:

```sh
cd lean
lake exe cache get
lake build
```

The manifest pins Mathlib. The five modules check the endpoint polynomial derivative, heat differentiation and downward shifts, the bracket and three-region implications, geometric remainder estimates, and finite arithmetic for the supplied coefficient boxes. The sign module retains a regression check against five rounded bounds from the previous draft. Identifying the concrete Xi kernel's coefficients with those boxes and establishing its full Fourier and regional hypotheses remain external to Lean.
