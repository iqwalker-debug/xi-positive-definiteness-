# Paper V — Five spatial covariance values suffice
Ian Walker · Working draft · November 27, 2026

[Manuscript](Paper-V.pdf) · [LaTeX](Paper-V.tex) · [Verifier](verify.py)

From a checkout of this repository, with Python 3.12 and assertions enabled:

```sh
python -m pip install python-flint==0.8.0 sympy==1.14.0
python paper-v/verify.py
```

The default run checks all 64 subsets twice. It uses the zeta–gamma formula and the separate theta quadrature in Paper IV, then checks overlap of all moment enclosures. The verifier needs the sibling `paper-iv/audit-numeric/matrix.py` from the checkout. The rational witnesses are given in full in the paper. To rebuild the PDF, run `pdflatex Paper-V.tex` twice in this directory.
