#!/bin/bash
# Run Bitwuzla 0.9.0-dev on the 66-benchmark SMT-COMP QF_BV sample
# from §4.5 of Paper 2. 60s timeout to match the existing
# CBMC / cvc5 measurements.

set -u
ROOT=$(realpath "$(dirname "$0")/..")
cd "$ROOT"

BITWUZLA=/home/ubuntu/bitwuzla.git/build/src/main/bitwuzla
TIMEOUT=60
SAMPLE=$ROOT/bench-multiplication/smt-comp-sample
OUT=$ROOT/bench-multiplication/smt-comp-bitwuzla.tsv

ulimit -v 57591731 2>/dev/null || true

cat > "$OUT" <<HEADER
# Bitwuzla 0.9.0-dev on the SMT-COMP QF_BV 66-benchmark sample
# 60s timeout, matching the cbmc / cvc5 measurements.
benchmark	time	result
HEADER

n=0
total=$(ls "$SAMPLE"/*.smt2 2>/dev/null | wc -l)
echo "Running $total benchmarks against Bitwuzla..." >&2

for f in "$SAMPLE"/*.smt2; do
  name=$(basename "$f" .smt2)
  out=$( { time -p timeout $TIMEOUT $BITWUZLA "$f" 2>/dev/null; } 2>&1 )
  rt=$(echo "$out" | grep -oE "real [0-9.]+" | awk '{print $2}')
  res=$(echo "$out" | grep -oE "^(sat|unsat|unknown)$" | head -1)
  if [ -z "$res" ] || [ "$res" = "unknown" ]; then
    rt="$TIMEOUT"
    res="T/O"
  fi
  printf '%s\t%s\t%s\n' "$name" "$rt" "$res" >> "$OUT"
  n=$((n+1))
  if (( n % 10 == 0 )); then echo "  $n / $total" >&2; fi
done

echo "Done ($n / $total). Output: $OUT" >&2
