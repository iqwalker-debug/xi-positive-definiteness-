# Heat-cutoff consequences

This module uses the real Gram-matrix predicate and the exact 739-shell witness from AxiomDraft. Its heat profile uses the theta series in ThetaCosine, the Fourier convention of Paper I, and the parameter λ of Paper II. The module proves implications with the following explicit inputs.

| Lean theorem | Conclusion checked by Lean | Inputs supplied externally for Xi |
|---|---|---|
| odd_endpoint_cutoff | A zero of the endpoint polynomial forces the last admissible dimension to be the given odd dimension. The integral of a nonzero continuous nonnegative radial density along the central line is strictly positive. | Paper II's root and odd-dimensional inclusion at each of the thirteen endpoints, and the Fourier projection formula identifying the central marginal with a scalar multiple of that polynomial. |
| heat_window_cutoff | On the entire closed interval from −1/1250 to 1/4, the exact cutoff is nine, given the displayed premises. Lean proves the polynomial and remainder arithmetic uniformly in λ, then applies the actual lattice-witness obstruction. | Dimension-nine positivity from Paper II, the Taylor expansion with its analytic tail bound for a positive rescaling of the compressed Gram form, and the certified coefficient boxes. |
| finite_ceiling | Every heat parameter satisfying the premises has an exact finite last dimension, at least one. | One-dimensional admissibility, three theta-value enclosures, and the implication from all-dimensional admissibility to a Gaussian-mixture representation at those radii (Schoenberg). |

The midpoint calculation is in squared radius. Normalizing the mixing law by its contribution at radius zero makes the middle and final values its first and second moments times the zero-radius value. Lean uses nonnegative variance, proves that the heat factors cancel, and finds a last dimension from the first failure. The Schoenberg representation theorem itself remains an input.

## Numerical interface

The Taylor proof uses the weaker rational bounds a₀ ≤ −0.01259, −15.13 ≤ a₁ ≤ −15.11, and |aⱼ| ≤ 5 for 2 ≤ j ≤ 12. On |λ| ≤ 1/4 the Horner tail with these coefficients has magnitude at most seven. The remaining error is bounded by 10¹¹ q¹³/(1−q) for q = |λ|/3. Lean proves this is at most λ². This removes the need for the 256 positive-side subdivision tests in the previous numerical check.

The analytic input to the error estimate uses Φ(r) ≤ 6 exp(−3r²), Z₀ = Ξ(0)/2 > 1/5, and the Gaussian moments. Each unsigned heat coefficient is bounded by (sum of normalized shell weights) × 30 sqrt(π/3) × 3^(−j). The Arb script checks the prefactor and the enclosures of the 13 computed coefficients. Lean does not evaluate zeta or prove this Fourier–Taylor identification.

For the midpoint test Arb gives 0 < Φ(0) < 1/2, Φ(sqrt(1/2)) > 1/1000 and 0 < Φ(1) < 1/5000000. The Lean proof uses the resulting strict inequality Φ(0) Φ(1) < Φ(sqrt(1/2))². The numerical enclosures remain outside Lean's kernel.

## Replay

In verification/lean, run:

    lake update
    lake exe cache get
    lake build XiHeatConsequences

In verification/arb, with the pinned requirements installed, run:

    python certify_heat_consequences.py --bits 192
    python certify_heat_consequences.py --bits 256

The file prints the axioms of the application theorems and their main lemmas. Numeric and analytic hypotheses appear in theorem statements and must still be supplied even when the axiom audit is clean. The negative-center Abel-inversion formula is not used in the marginal proof or formalized in this module.
