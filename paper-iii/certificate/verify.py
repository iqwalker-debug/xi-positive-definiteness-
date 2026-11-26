"""Recompute all witnesses and check the canonical witness list. Run from any directory."""
from hashlib import sha256
from pathlib import Path
import json
import sys

from certificate18 import certify

if __name__ == "__main__":
    if not __debug__:
        sys.exit("Use standard Python with assertions enabled.")
    witnesses, result = certify()
    if result["certified"] != 132606 or result["witnesses_sha256"] != "3f7c10abdc6af31fa40e650a264e7275de57e6baa88285357a7e6576c7c93417":
        sys.exit("Witness count or digest mismatch.")
    payload = "".join(f"{mask},{witnesses[mask]}\n" for mask in sorted(witnesses)).encode("ascii")
    path = Path(__file__).with_name("witnesses.csv")
    if path.exists() and sha256(path.read_bytes()).hexdigest() != result["witnesses_sha256"]:
        sys.exit("Bundled CSV disagrees with the recomputed witnesses.")
    if not path.exists():
        path.write_bytes(payload)
    print(json.dumps(result, indent=2))
