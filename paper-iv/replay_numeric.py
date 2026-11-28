"""Recompute the four independent Arb certificates and check their frozen intervals."""
from pathlib import Path
import re
import subprocess
import sys

from flint import arb, ctx

ROOT = Path(__file__).resolve().parent / "independent-numeric"
CASES = (
    ("fourier_certificate.py", "fourier-frozen.log"),
    ("postcomparison_controls.py", "postcomparison-controls.log"),
    ("postcomparison_h3.py", "postcomparison-h3.log"),
    ("spd/eigen_certificate.py", "spd/eigen_certificate.log"),
)
# The frozen text uses Arb's bracketed midpoint +/- radius notation.
BALL = re.compile(r"\[[^\[\]\n]+? \+/- [^\[\]\n]+?\]")


def compare_line(reference, output):
    if BALL.sub("BALL", reference) != BALL.sub("BALL", output):
        raise ValueError("output labels or number of enclosures differ")
    expected = [arb(value) for value in BALL.findall(reference)]
    actual = [arb(value) for value in BALL.findall(output)]
    if reference.lstrip().startswith("[["):
        # LAPACK proposes the basis; compare certified eigenvalue intervals, not
        # the last digits of the left and right boundaries of different bases.
        left, right = actual
        saved_left, saved_right = expected
        if not left < right or not right - left < arb("1e-10"):
            raise ValueError("recomputed eigenvalue interval is inverted or too broad")
        if not left.union(right).overlaps(saved_left.union(saved_right)):
            raise ValueError("certified eigenvalue intervals are disjoint")
        return
    for current, saved in zip(actual, expected):
        if not current.is_finite() or not current.overlaps(saved):
            raise ValueError("recomputed result misses the frozen enclosure")
        if current.rad() > 2 * saved.rad():
            raise ValueError("recomputed enclosure lost precision")


def main():
    ctx.prec = 512
    for script, reference_log in CASES:
        result = subprocess.run(
            [sys.executable, str(ROOT / script)], cwd=ROOT, text=True,
            stdout=subprocess.PIPE, check=True,
        )
        print(result.stdout, end="", flush=True)
        saved = (ROOT / reference_log).read_text().splitlines()
        current = result.stdout.splitlines()
        if len(saved) != len(current):
            raise ValueError(f"{script}: expected {len(saved)} output lines, got {len(current)}")
        for number, (expected, obtained) in enumerate(zip(saved, current), start=1):
            try:
                compare_line(expected, obtained)
            except ValueError as exc:
                raise ValueError(f"{script}, line {number}: {exc}") from exc
        print(f"PASS {script} ({reference_log})", flush=True)


if __name__ == "__main__":
    main()
