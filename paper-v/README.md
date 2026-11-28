# Paper V — Five spatial covariance values suffice
Ian Walker · Working draft · November 27, 2026

[Manuscript](Paper-V.pdf) · [LaTeX](Paper-V.tex) · [Verifier](verify.py)

From a checkout of this repository, with Python 3.12 and assertions enabled:

```sh
python -m pip install python-flint==0.8.0 sympy==1.14.0
python paper-v/verify.py
```

The default run checks all 64 subsets twice. It uses the zeta–gamma formula and the separate theta quadrature in Paper IV, then checks overlap of all moment enclosures. The verifier needs the sibling `paper-iv/audit-numeric/matrix.py` from the checkout. The rational witnesses are given in full in the paper. To rebuild the PDF, run `pdflatex Paper-V.tex` twice in this directory.

### Lean and Arb verification

Run the Arb verifier above, then check the generated Lean certificate with Lean 3.51.1 and the compiled mathlib3 revision `65a1391a0106c9204fe45bc73a039f056558cb83`. The four public polynomial lemmas end in `_nonneg`. They prove both signed differences are nonnegative on the entire real interval [−1,1] for each excluding design. Lean expands the Chebyshev recursion and checks the polynomial identity on each dyadic cell. The coverage theorem checks all six Boolean inputs and proves the feasible and excluded descriptions are complements.

```sh
cd paper-v
python formal/generate.py
python formal/generate_fields.py
git diff --exit-code -- formal/Certificates.lean formal/DesignFields.lean
bash formal/replay.sh
```

Set `LEAN_BIN` to the Lean executable and `MATHLIB3_SRC` to the pinned mathlib3 src directory if they are outside the default search path. The generator reads the exact coefficients and missing-index sets from verify.py. Lean checks the emitted proof independently of the generator. The archived output lists axioms for each public theorem.

### Constructive field existence

In `formal/Field.lean`, each harmonic contributes four real sine/cosine trajectories paired with their negatives. The theorem `finite_centered_field` checks that the resulting finite probability weights sum to one, every single-location mean is zero, and every pairwise covariance is the prescribed function of the space and time differences. The covariance is continuous and spatially reflection-symmetric. Stationarity here concerns second moments.

In `formal/DesignFields.lean`, `feasible_subsets` constructs a covariance for every feasible subset and every common nonzero time lag. Each maximal design uses seven or eight spatial/temporal frequency pairs. Lean checks positivity of the interpolating weights, normalization, both delayed readings, and the prescribed equal-time values throughout the rational moment intervals. The construction provides an alternative to the matrix witnesses in the paper. The general truncated trigonometric moment theorem used in Section 2 is not a hypothesis of this Lean proof.

Arb supplies the six Xi moment inequalities used to specialize Lean's real-parameter theorem. Both the zeta–gamma and theta-integral routes check these inequalities, the 70 matrix minors, and the two exclusion ceilings. They share the FLINT/Arb library. The Lean scope does not include evaluation of the Xi function, the general Toeplitz representation theorem for arbitrary inputs, or strict stationarity of all joint distributions.
