# Sharp space–time covariance bounds for the Riemann Xi profile

Paper IV is an AI-assisted working manuscript prepared for Ian Walker, revision 2, dated 26 November 2026. External specialist review is pending. [Read the eleven-page paper](Paper-IV.pdf) or [inspect the editable manuscript](manuscript/manuscript.md).

Suppose a stationary, real scalar field has a prescribed equal-time spatial covariance and is spatially isotropic at each time lag. How large can the delayed correlation between two locations be? The paper shows that the sharp bound is the average absolute value of the spherical Fourier kernel against the fixed radial spectrum. It gives the exact criterion for strict improvement under dimension projection. For several distinct positive separations at the same nonzero time lag, it proves strict containment of the entire attainable region when the higher-dimensional radial frequency has unbounded support. Applying the result to Xi through dimension nine uses the spatial theorem in [Paper I](../Paper-I.pdf).

At spatial separations 8 and 16, a ten-observation covariance matrix accepts the pair (0.50, 0.50) and has smallest eigenvalue about 0.02466249. The full Xi spectrum bounds the sum of these readings by 0.9294554312364952. Replacing Xi by a Gaussian matched in spectral variance increases the sum bound and decreases the difference bound.

## Verification and scope

| Evidence | How to reproduce |
|---|---|
| Independent interval calculations of the Xi and Gaussian supports, the ten-observation minimum eigenvalue, and the 3D bound | Install the packages in `requirements-ci.txt` with Python 3.12 and run `python replay_numeric.py` in this directory. The individual scripts and expected results are in [independent-numeric](independent-numeric). |
| Original one-separation certificates | In [single_lag](single_lag), run `python xi_covariance_envelope.py` and `python xi_d3.py` with python-flint 0.8.0. Compare with the two supplied JSON files. |
| Original two-separation certificates, Gaussian control and finite matrix | Follow the instructions in [two_radii](two_radii/README.md) with python-flint 0.9.0 in a separate environment. Both interval implementations use Arb. |
| Projection to dimensions 1–9 | Run `python dimension_projection/gennew_ladder.py` with NumPy, SciPy and mpmath. It produces a floating-point quadrature table. Its even-dimensional entries are numerical illustrations. |
| Twelve Lean declarations | Run `bash formal/replay.sh` with Lean 3.51.1 and the [pinned mathlib3 revision](formal/README.md). Four declarations concern finite covariance algebra and eight concern strict integration and projection. The sphere and Bessel inputs, the Xi specialization, and the new joint-region corollary have written proofs. |
| Acoustic parity control | The [recording and replay instructions](acoustic/README.md) specify the public source WAV, reference checksums, acquisition intervals and two implementations. The 52 held-out comparisons use one recording in one room. |

## Manuscript and plots

The plotted boundaries sample the support functions described in the paper. Numerical enclosures are recorded separately in the certificate files. To regenerate the plot files, install NumPy, SciPy and Matplotlib, then run these commands from this directory:

```sh
python manuscript/plot-envelopes.py
python manuscript/plot-projection.py
python two_radii/figure.py
```

To rebuild the PDF, install Pandoc, Chromium, the DejaVu and Latin Modern math fonts, and Python packages `playwright` and `pymupdf`. Run `python manuscript/render.py`. Set `CHROME_PATH` to a Chromium executable if it is not available as `chromium` on the executable path. The renderer checks that the equations and images loaded, verifies the page count and adds bookmarks.

The bibliography credits the existing space–time representation, radial dimension projection, covariance constraints and Xi line law. Scientific priority remains subject to specialist assessment.
