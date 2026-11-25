# Verification of the normalized radial Xi cutoff

The radial kernel with profile Re(ξ(1/2+it)/ξ(1/2)) is strictly positive definite on distinct points in dimensions 1 through 9. A finite Gram witness in dimension 10 rules out positive semidefiniteness there and in all higher dimensions.

## Lean and Arb boundary

- `GenesisTidalMellin.strict_d9` has no numerical enclosure hypotheses. It uses the exact Xi cosine identity, an integrable density positive almost everywhere, direct theta-series sign proofs, and the linear independence of distinct exponential characters.
- `GenesisTidalMellin.strict_cutoff_of_arb` combines the D9 theorem with the exact D10 witness algebra. Its two hypotheses are the lists of pointwise upper enclosures of the 294 retained and 445 remaining finite shell contributions. Lean checks the summation, negativity, and propagation to higher dimensions.
- Arb and Acb establish those enclosure hypotheses externally. At 192 and 256 bits the workflow re-evaluates all 739 nonzero shell contributions and compares the rounded upper bounds with the exact Lean table. It also runs an aggregate finite-sum check and replays both D9 tables as an independent cross-check of the analytic signs.

## Reproduce

Run the Mathematical Verification workflow on the pinned source. The lean-evidence artifact gives the compiled theorem and axiom audit. The two Arb evidence artifacts include the D9 bounds, the D10 row tables, and the aggregate D10 replay.

The formal statement uses real coefficient vectors. The kernel is real and symmetric, so positive definiteness for complex coefficients follows by applying the real quadratic form to the real and imaginary parts separately.
