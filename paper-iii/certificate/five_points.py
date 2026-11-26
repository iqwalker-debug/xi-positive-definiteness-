"""Reproduce the five-point Paper III certificate, using only Python's standard library."""
import argparse
import json
from pathlib import Path
import certificate18 as cert

SCALES = (4, 52, 212, 695, 1438)

ORIGINAL = cert.SCALES

def check(output_path=None, combined=False):
    if not __debug__:
        raise RuntimeError("Use Python without -O so all certificate assertions run.")
    cert.SCALES = tuple(sorted(set(ORIGINAL) | set(SCALES))) if combined else SCALES
    witnesses, result = cert.certify()
    if result["certified"] != (133315 if combined else 131854):
        raise ArithmeticError("Unexpected number of certified sign patterns")
    result["denominators"] = cert.SCALES
    result["new_at_each_scale"] = [v - u for u, v in zip([0] + result["cumulative"], result["cumulative"])]
    if output_path is not None:
        rows = "".join(f"{mask},{witnesses[mask]}\n" for mask in sorted(witnesses))
        output_path.write_bytes(rows.encode("ascii"))
    return result

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--csv", type=Path, help="write the sorted mask,denominator table")
    parser.add_argument("--combined", action="store_true", help="test both grids together")
    args = parser.parse_args()
    print(json.dumps(check(args.csv, args.combined), indent=2))
