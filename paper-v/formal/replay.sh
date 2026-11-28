#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean_bin=${LEAN_BIN:-lean}
if [[ -n ${MATHLIB3_SRC:-} ]]; then
  base_path=$("$lean_bin" --path | python3 -c 'import json,sys; print(":".join(json.load(sys.stdin)["path"]))')
  export LEAN_PATH="${MATHLIB3_SRC}:${base_path}"
fi
"$lean_bin" --version
"$lean_bin" -j 2 Certificates.lean
