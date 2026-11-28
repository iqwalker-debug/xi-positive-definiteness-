# xi-positive-definiteness-

## How to cite these papers

For Papers I–IV, cite Ian Walker and the title of the manuscript containing the result. The [paper-specific BibTeX entries](papers.bib) link to the exact manuscript versions. For the collection and its verification materials, use the [repository citation](CITATION.cff).

## Paper I

[The Exact Positive-Definiteness Dimension of the Riemann Xi Function](Paper-I.pdf) by Ian Walker. [Zenodo DOI](https://doi.org/10.5281/zenodo.24614006).

The November 27 revision compares the derivative recurrences in Section 1 and identifies the numerical hypotheses of the Lean cutoff theorem beside Theorem 1.

### Check the original verification run

At commit `b852248`, both Arb jobs printed the total interval `[-12596367123836528, -12596367123835788]` in units of `10^-18`. The Lean job printed `[propext, Classical.choice, Quot.sound]` for both `strict_d9` and `strict_cutoff_of_arb`. The latter declaration takes the shell upper bounds as explicit hypotheses.

| Original job log | SHA-256 of the evidence ZIP uploaded by that job |
|---|---|
| [Arb, 192 bits](https://github.com/iqwalker-debug/xi-positive-definiteness-/actions/runs/45646086586/job/139317344510) | `9edcc8b88d817e28c2149890d5fba101bec27f722c73bbc9aa0c10f843fa7530` |
| [Arb, 256 bits](https://github.com/iqwalker-debug/xi-positive-definiteness-/actions/runs/45646086586/job/139317344794) | `fa4daf5050f68b70e949f097fb1b46cc6e0e9650b3f0065a46c2eea815d7acd4` |
| [Lean theorem and axiom audit](https://github.com/iqwalker-debug/xi-positive-definiteness-/actions/runs/45646086586/job/139317344090) | `96cdba30eda0c6dc44b1236111cbc4b49127a8926ce19f5369694ee67012dd85` |

### Reproduce the ten-dimensional counterexample

The [theta-integral verification note](supplements/d10-theta/Verification-note.pdf) derives the error bounds for a second evaluation of the paper’s finite witness. The [replay package](supplements/d10-theta/Paper-I-D10-Theta-Verification.zip) contains the Python checker, reference intervals, all 739 computed shell contributions at each mesh, and SHA-256 checksums.

After extracting the ZIP, run these commands from the extracted directory with Python 3.12 and its standard library:

```sh
python -I verify.py --mesh 160 --reference reference --output rerun-160.json
python -I verify.py --mesh 192 --reference reference --output rerun-192.json
```

Both meshes reproduce a strictly negative normalized Gram sum of approximately −0.012596367123836187. Each of the 739 computed contributions lies inside its archived interval. This calculation uses the theta integral and integer interval arithmetic with decimal exponentials. The [original certificate](https://github.com/iqwalker-debug/xi-positive-definiteness-/tree/b85224897e27d51141b85c98bad5173c78211dce/verification) uses Arb/Acb. The two calculations share the witness and its normalization.

## Paper II

[Positive-Definiteness Endpoints of Heat-Deformed Riemann Xi Kernels](paper-ii/Paper-II.pdf) by Ian Walker. This preprint gives the exact heat-parameter endpoints for positive semidefiniteness in odd Euclidean dimensions from 3 through 27. It awaits independent human review.

[LaTeX source](paper-ii/Paper-II.tex) · [Certificates, Lean checks, and reproduction instructions](paper-ii/README.md)

## Paper III

[Finite witnesses for failure of positive definiteness in quadratic Dirichlet L-functions](paper-iii/Paper-III.pdf) by Ian Walker. [Zenodo DOI](https://doi.org/10.5281/zenodo.24614710). Using the first 18 prime signs, truncation at 300, and individual upper bounds on unresolved terms, five common theta points are necessary and sufficient to certify a strict majority of the prime sign patterns.

[LaTeX source](paper-iii/Paper-III.tex) · [Reproduction instructions and counts](paper-iii/README.md) · [Certificate code and witness tables](paper-iii/certificate)

## Paper IV

[Sharp space–time covariance bounds for the Riemann Xi profile](paper-iv/Paper-IV.pdf) is a revision 4 working draft by Ian Walker. Two delayed correlations of 0.50 pass a ten-observation covariance test, yet the full Xi spatial profile limits their sum to approximately 0.9294554312. The paper derives this bound from the fixed radial spectrum and proves strict contraction of the joint region under dimension projection. Its Xi application uses Paper I. An acoustic control reports the intervening microphone windows, including a reversal under both frequency weightings. External specialist review and priority assessment remain open.

[Manuscript source, figures, Lean and Arb checks](paper-iv/README.md)
