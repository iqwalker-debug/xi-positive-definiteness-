#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
cd certificate
w=$(mktemp -d)
trap 'rm -rf "$w"' EXIT
python3 verify.py > "$w/original.json"
cmp "$w/original.json" replay-output.json
python3 scales.py > "$w/scale-results.json"
cmp "$w/scale-results.json" scale-results.json
python3 five_points.py --csv "$w/five.csv" > "$w/five.json"
cmp "$w/five.json" expected.json
cmp "$w/five.csv" five-witnesses.csv
python3 five_points.py --combined --csv "$w/combined.csv" > "$w/combined.json"
cmp "$w/combined.json" expected-combined.json
cmp "$w/combined.csv" combined-witnesses.csv
python3 compare.py > "$w/compare.txt"
cmp "$w/compare.txt" comparison.txt
cat "$w/compare.txt"
python3 lookup.py 2339
python3 witness.py
python3 sensitivity.py
python3 enclose.py "$w/first.bin" --subdivisions 128
echo "433a31662e825baaf2e5682d4fbe233651f24bf18e4372eb05e9b39926811b30  $w/first.bin" | sha256sum -c -
python3 cover.py "$w/first.bin" --limit 129903
g++ -std=c++17 -O2 -fsanitize=undefined -fno-sanitize-recover=all tangent.cpp -o "$w/tangent"
"$w/tangent" "$w/second.bin"
echo "bb5cad04f12ec10b33d63681bcced7ed2a3593caf02cfa55807b39a9677006da  $w/second.bin" | sha256sum -c -
python3 check_tree.py "$w/second.bin" 129901
python3 check_containment.py "$w/first.bin" "$w/second.bin"
echo "All manuscript certificate checks passed."
