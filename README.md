# xi-positive-definiteness-

## Paper I

[The Exact Positive-Definiteness Dimension of the Riemann Xi Function](Paper-I.pdf) by Ian Walker.

### Reproduce the ten-dimensional counterexample

The [theta-integral verification note](supplements/d10-theta/Verification-note.pdf) derives the error bounds for a second evaluation of the paper’s finite witness. The [replay package](supplements/d10-theta/Paper-I-D10-Theta-Verification.zip) contains the Python checker, reference intervals, all 739 computed shell contributions at each mesh, and SHA-256 checksums.

After extracting the ZIP, run these commands from the extracted directory with Python 3.12 and its standard library:

```sh
python -I verify.py --mesh 160 --reference reference --output rerun-160.json
python -I verify.py --mesh 192 --reference reference --output rerun-192.json
```

Both meshes reproduce a strictly negative normalized Gram sum of approximately −0.012596367123836187. Each of the 739 computed contributions lies inside its archived interval. This calculation uses the theta integral and integer interval arithmetic with decimal exponentials. The [original certificate](https://github.com/iqwalker-debug/xi-positive-definiteness-/tree/b85224897e27d51141b85c98bad5173c78211dce/verification) uses Arb/Acb. The two calculations share the witness and its normalization.
