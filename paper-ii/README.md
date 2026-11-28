# Positive-Definiteness Endpoints of Heat-Deformed Riemann Xi Kernels

[Paper II](Paper-II.pdf) by Ian Walker is a working draft awaiting human review. Theorem 5 gives exact endpoints for odd dimensions 3 through 27. The next odd-dimensional case in Conjecture 6 is 29. The paper gives bounds on even-dimensional endpoints.

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
```

| Certificate | Coverage and arithmetic |
|---|---|
| `certify_bounds.py` | Thirteen root brackets at 256 and 384 bits in Arb. Each `derivative_upper_on_bracket` string is the exact dyadic upper endpoint expressed as a rational numerator/denominator. |
| `certify_sharp.py` | Three-region sharpness checks for every odd dimension from 5 through 27, at 512 and 768 bits in Arb. |
| `check_d3.py` | Independent cross-check of the dimension-three inequality at 128 and 192 bits. |
| [Integer verifier](integer/README.md) | A second implementation checks the same brackets and sharpness range using directed integer arithmetic and separate Taylor coefficient calculations. |

The Paper II GitHub Actions workflow reruns Arb, checks all 26 exported bounds at 768 bits, replays the integer verifier, and compares the regenerated bounds and sharpness files byte for byte. The logs report both precisions and every dimension.

`check_export.py` also verifies the D5 origin inequality used with second-level log-concavity. In `heat-upper-bounds.json`, `lower` and `upper` are the exact rational endpoints. The legacy scalar `enclosure` is the lower endpoint converted to a float.

## Reproduce the Lean checks

With the Lean toolchain manager installed, run:

```sh
cd lean
lake exe cache get
lake build
```

The manifest pins Mathlib. The five endpoint modules check the endpoint polynomial derivative, heat differentiation and downward shifts, the bracket and three-region implications, geometric remainder estimates, and finite arithmetic for the supplied coefficient boxes. The sign module retains a regression check against five rounded bounds from the previous draft. Identifying the concrete Xi kernel's coefficients with those boxes and establishing its full Fourier and regional hypotheses remain external to Lean.

The sixth module, [GaussianTilt.lean](lean/GaussianTilt.lean), checks the Gaussian shell expansion under the integral for signed tests, positivity of projected cosine Gram forms given the marginal identity, positivity after radius mixing and normalization, and the final cutoff implication. To inspect its axiom report, run `lake env lean GaussianTilt.lean` from the Lean directory.

The application to Xi uses the classical radial spectral representation and the projected sphere marginal formula from the manuscript. The Lean module takes geometric identities as hypotheses. The final cutoff lemma also takes the D9 overlap, D10 obstruction, downward closure in D10, dimension restriction, and the nonnegative real-zero threshold as hypotheses. Connecting all these inputs for the concrete Xi profile remains outside this formalization.
