"""Replay Paper IV's finite matrix, dimension gap and scalar profile certificates."""
import json
from pathlib import Path

import dimension_gap
import matrix
import profile_checks


if __name__ == "__main__":
    references = json.loads(Path(__file__).with_name("certificates.json").read_text(encoding="utf-8"))
    profile_checks.verify(references["fourth_derivatives"], references["three_dimensional_asymptotic"])
    matrix.verify(references["minimum_eigenvalue"])
    dimension_gap.verify(references["dimension_gap"])
