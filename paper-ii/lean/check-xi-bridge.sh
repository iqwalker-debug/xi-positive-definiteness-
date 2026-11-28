#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
out="$PWD/.lake/build/xi-bridge"
mkdir -p "$out"
export LEAN_PATH="$out:$(lake env printenv LEAN_PATH)"
for mod in AxiomDraft D9Coverage D9Fourier D9Mellin ThetaSeries ThetaCosine ThetaJets PositiveWalk XiProfile XiCutoff; do
  (cd ../../verification/lean && lean -o "$out/$mod.olean" "$mod.lean")
done
lean -o "$out/EndpointHeat.olean" EndpointHeat.lean
lean XiCoexistence.lean
