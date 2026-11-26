# Sharp space–time covariance bounds for the Riemann Xi profile

Paper IV is an AI-assisted working manuscript prepared for Ian Walker, revision 3, dated 26 November 2026. External specialist review is pending. [Read the paper](Paper-IV.pdf) or [inspect the manuscript](manuscript/manuscript.md).

Suppose a stationary, real scalar field has a prescribed equal-time spatial covariance and is spatially isotropic at each time lag. How large can the delayed correlation between two locations be? The paper shows that the sharp bound is the average absolute value of the spherical Fourier kernel against the fixed radial spectrum. It gives the exact criterion for strict improvement under dimension projection. For several distinct positive separations at the same nonzero time lag, it proves strict containment of the entire attainable region when the higher-dimensional radial frequency has unbounded support. Applying the result to Xi through dimension nine uses the spatial theorem in [Paper I](../Paper-I.pdf).

At spatial separations 8 and 16, a ten-observation covariance matrix accepts the pair (0.50, 0.50) and has smallest eigenvalue about 0.02466249. The full Xi spectrum bounds the sum of these readings by 0.9294554312364952. The pair sums to 1.00, exceeding this upper limit by more than 0.07054. A Gaussian matched to Xi in curvature at the origin increases the sum bound and decreases the difference bound. The dimension comparison keeps the entire spatial profile fixed and projects its radial spectral law.

## Verification and scope

| Evidence | How to reproduce |
|---|---|
| Independent interval calculations of the Xi and Gaussian supports, the ten-observation minimum eigenvalue, and the 3D bound | Install the packages in `requirements-ci.txt` with Python 3.12 and run `python replay_numeric.py` in this directory. The individual scripts and expected results are in [independent-numeric](independent-numeric). |
| New interval certificates for the minimum eigenvalue and the 8D–9D gap | Run `python audit-numeric/replay.py`. The [derivations and rational endpoints](audit-numeric/README.md) certify the eigenvalue between shifts spaced by 10⁻³⁵ and enclose the gap at separation 5 strictly between 3.38500 × 10⁻¹² and 3.42424 × 10⁻¹². |
| Original one-separation certificates | In [single_lag](single_lag), run `python xi_covariance_envelope.py` and `python xi_d3.py` with python-flint 0.8.0. Compare with the two supplied JSON files. |
| Original two-separation certificates, Gaussian control and finite matrix | Follow the instructions in [two_radii](two_radii/README.md) with python-flint 0.9.0 in a separate environment. Both interval implementations use Arb. |
| Projection to dimensions 1–9 | Run `python dimension_projection/gennew_ladder.py` with NumPy, SciPy and mpmath. It produces a floating-point quadrature table. This script is illustrative. The separate interval calculation above certifies the specific 8D–9D gap at separation 5. |
| Twelve Lean declarations | Run `bash formal/replay.sh` with Lean 3.51.1 and the [pinned mathlib3 revision](formal/README.md). Four declarations concern finite covariance algebra and eight concern strict integration and projection. The sphere and Bessel inputs, the Xi specialization, and the new joint-region corollary have written proofs. |
| Acoustic parity control | The [recording and replay instructions](acoustic/README.md) specify the public source WAV, reference checksums, acquisition intervals and two implementations. The two original held-out windows and all five intervening eight-second windows use one recording, with two frequency weightings over 200–1600 Hz. At 54–62 s all 13 oriented pairs reverse sign relative to training under each weighting. Run `python acoustic/replay_windows.py --check-stored` to verify the stored pairwise data and error summaries. The acoustic README gives the raw-recording replay. |

## Checking the printed results

Edit [manuscript.template.md](manuscript/manuscript.template.md), then run `python verify_claims.py --write` from this directory to regenerate the Markdown. Run `python verify_claims.py --check` to compare the manuscript with the certificate-derived text, `python verify_claims.py --self-test` to confirm that altered values are caught, and `python manuscript/pdf_provenance.py` to check the source and figure fingerprint embedded in the PDF. The GitHub workflow also reruns Arb and Lean.

## Manuscript and plots

The plotted boundaries sample the support functions described in the paper. Numerical enclosures are recorded separately in the certificate files. To regenerate the plot files, install NumPy, SciPy and Matplotlib, then run these commands from this directory:

```sh
python manuscript/plot-envelopes.py
python manuscript/plot-projection.py
python two_radii/figure.py
python acoustic/plot_windows.py
```

To rebuild the PDF, install Pandoc, Chromium, the DejaVu and Latin Modern math fonts, and Python packages `playwright` and `pymupdf`. Run `python manuscript/render.py`. Set `CHROME_PATH` to a Chromium executable if it is not available as `chromium` on the executable path. The renderer checks that the equations and images loaded, verifies the page count and adds bookmarks.

The bibliography credits the existing space–time representation, radial dimension projection, covariance constraints and Xi line law. Scientific priority remains subject to specialist assessment.
