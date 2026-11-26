# Lean verification of strict radial projection

The referee replay on 26 November 2026 checked eight new measure-theoretic declarations in `StrictProjection.lean` and all four original declarations in `CovarianceGram.lean`. Both source files exited successfully under Lean 3.51.1 (commit `cce7990ea86a`). The original source is byte-identical to the supplied manuscript bundle. Each declaration reports only `propext`, `classical.choice` and `quot.sound` in its transitive axiom inventory. The complete fresh Lean output is in `replay.log`. All new proofs are ordinary Lean theorems with explicit hypotheses.

## The checked statement

Let ν and κ be finite real Borel measures. Suppose ν gives positive mass to every upper tail and κ gives positive mass to every nonempty open subset of (0,1). Let Ω be continuous with |Ω| ≤ 1 and with both a positive and a negative value at positive arguments. Define Ψ(z) by averaging Ω(zb) against κ. Let μ be the pushforward of ν × κ by (r,b) ↦ rb. Then, for every a > 0,

    ∫ |Ψ(ar)| ν(dr) < ∫ |Ω(as)| μ(ds).

In the manuscript, Ω is the lower-dimensional angular characteristic function, Ψ is its higher-dimensional counterpart, ν is the higher-dimensional radial law and μ is the lower-dimensional radial law. The argument works with any sign witnesses on the positive half-line. Locating the first Bessel zero is unnecessary for the formal comparison.

| Declaration | Mathematical content |
|---|---|
| `integral_pos_of_witness` | An a.e. nonnegative integrable gap has positive integral when it is positive on a set of positive measure. |
| `integral_lt_of_witness` | Transfers a positive-measure strict comparison through the integral. |
| `abs_integral_lt_integral_abs` | If an integrable real random variable takes each sign with positive mass, its absolute integral is strictly less than the integral of its absolute value. |
| `strict_projection_envelope` | Applies the angular strict inequality on a positive-measure radial witness and integrates the gap. |
| `angular_both_signs` | Uses continuity and angular support to obtain two positive-mass sign sets by scaling the two sign points into (0,1). |
| `strict_radial_projection` | Selects the radial tail where the scaled sign witnesses both occur. |
| `strict_bounded_radial_projection` | Derives each inner and outer integrability condition from bounded continuity and finite measures. |
| `adjacent_envelopes_of_projection` | Applies the angular averaging identity and the product pushforward, changes variables, and uses Fubini to compare the two envelopes. |

## Scope of the Xi specialization

The application still requires proofs that Euclidean sphere projection has the stated angular averaging identity and the radial product law, that its projection length law charges open subsets of (0,1), that each angular kernel has the required continuity, bound and two sign witnesses, and that the Xi radial law charges every upper tail. The paper provides mathematical arguments or cites inputs for these steps. This source does not identify concrete Xi spectral measures, establish positive definiteness through dimension nine, rule out dimension ten, or instantiate the comparison at the eight concrete adjacent pairs. The endpoint comparisons |F(a)| < H₉(a) and H₁(a) < T(a) and the sharp space–time extension theorem remain outside this verification. The first endpoint can use `abs_integral_lt_integral_abs` after discharging its concrete sign hypotheses.

## Replay

Use the manuscript's pinned mathlib3 revision `65a1391a0106c9204fe45bc73a039f056558cb83` with its compiled modules and Lean 3.51.1. An installed project already configured to find mathlib can run `bash replay.sh`. Otherwise, invoke the script with explicit paths from the directory containing this README.

    LEAN_BIN=/path/to/lean MATHLIB3_SRC=/path/to/mathlib3/src bash replay.sh

Python 3 is used to parse Lean's configured search path when `MATHLIB3_SRC` is set. The reviewer re-elaborated both source files against the locally available compiled mathlib cache. The compiler and mathlib were not independently rebuilt from source. The environment archive fingerprints below identify the bytes used. The delivered source and result file fingerprints are in `SHA256SUMS`.

| Cached archive | SHA-256 |
|---|---|
| Lean 3.51.1 Linux archive | `34c6e65d90f6b9161b2b5acdfb24baf8f3d59ec20d5090ba9688bf8a9b0765aa` |
| Compiled mathlib3 archive | `a12ac02e6d7748e5e38eb96d8182ac75f7332f578d8d6cb8a668a2ae578c586e` |
