#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean_bin=${LEAN_BIN:-lean}
if [[ -n ${MATHLIB3_SRC:-} ]]; then
  base_path=$("$lean_bin" --path | python3 -c 'import json,sys; print(":".join(json.load(sys.stdin)["path"]))')
  export LEAN_PATH="${MATHLIB3_SRC}:${base_path}"
fi
# Build from clean sources so an existing olean cannot mask a changed proof.
proof_dir=$(mktemp -d)
trap 'rm -rf "$proof_dir"' EXIT
cp Certificates.lean Field.lean DesignFields.lean "$proof_dir/"
cd "$proof_dir"
"$lean_bin" --version
"$lean_bin" -j 2 Certificates.lean
"$lean_bin" -j 2 --make Field.lean
"$lean_bin" -j 2 DesignFields.lean
