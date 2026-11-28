#!/usr/bin/env bash
# With the original versions installed, use `bash replay.sh` or set the environment below.
set -euo pipefail
cd "$(dirname "$0")"
lean_bin=${LEAN_BIN:-lean}
if [[ -n ${MATHLIB3_SRC:-} ]]; then
  base_path=$("$lean_bin" --path | python3 -c 'import json,sys; print(":".join(json.load(sys.stdin)["path"]))')
  export LEAN_PATH="${MATHLIB3_SRC}:${base_path}"
fi
"$lean_bin" --version
for source in CovarianceGram.lean StrictProjection.lean; do
  if grep -En '^[[:space:]]*(axiom|constant|meta[[:space:]]+(lemma|theorem))\b|\b(sorry|admit)\b' "$source"; then
    echo "Unexpected proof placeholder or axiom in $source" >&2
    exit 1
  fi
  echo "Checking $source"
  "$lean_bin" -j 1 "$source"
  echo "PASS $source"
done
