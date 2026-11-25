# Paper II (working draft, not reviewed)

`Paper-II.pdf` is an unreviewed draft: *Positive-Definiteness Endpoints of Heat-Deformed Riemann Xi Kernels*.
No person has checked its proofs yet. Do not cite it.

## Replaying the certificates

    python -m pip install -r requirements.txt
    python certify_bounds.py   # upper bounds, odd dimensions 3 to 27 (256 and 384 bits)
    python certify_sharp.py    # exact endpoints, dimensions 5 to 13 (512 and 768 bits)
    python check_d3.py         # dimension-three cross-check (128 and 192 bits)

Each script ends by printing `OK` or its results and rewrites its JSON file. The workflow
`Paper II certificates` runs all three and compares the regenerated JSON with the committed files.

The certificates were written with AI assistance (Claude). They use Arb ball arithmetic through
python-flint; nothing here is formalized in Lean.
