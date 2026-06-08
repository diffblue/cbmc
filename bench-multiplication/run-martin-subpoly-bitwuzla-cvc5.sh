#!/bin/bash
# Run Bitwuzla and cvc5 on the 210-benchmark random-polynomial sample
# (Martin's subpolynomial-encoding suite). Output augments the existing
# martin-subpoly-comparison-v2.tsv with two new columns.
#
# Used to validate the "18 wins beyond all current solvers" claim
# in Paper 2's two-pronged headline (decision point 1 of the
# 2026-05-26 structural rewrite plan).

set -u
ROOT=$(realpath "$(dirname "$0")/..")
cd "$ROOT"

BITWUZLA=/home/ubuntu/bitwuzla.git/build/src/main/bitwuzla
CVC5=/usr/local/bin/cvc5
TIMEOUT=10
MARTIN_DIR=/tmp/martin-bench
INPUT_TSV=$ROOT/bench-multiplication/martin-subpoly-comparison-v2.tsv
OUTPUT_TSV=$ROOT/bench-multiplication/martin-subpoly-bitwuzla-cvc5.tsv

ulimit -v 57591731 2>/dev/null || true

# Derive the SMT2 file path from the benchmark name
benchmark_path() {
  local name=$1
  if [[ $name == *seed-23* ]]; then
    echo "$MARTIN_DIR/seed-23/${name}.smt2"
  else
    echo "$MARTIN_DIR/seed-42/${name}.smt2"
  fi
}

# Run a single solver on a single benchmark, return time-or-TO
run_solver() {
  local solver=$1; local file=$2
  local cmd
  case $solver in
    bitwuzla) cmd="$BITWUZLA $file" ;;
    cvc5)     cmd="$CVC5 $file" ;;
    *) echo "T/O"; return ;;
  esac
  local out
  out=$( { time -p timeout $TIMEOUT $cmd 2>/dev/null; } 2>&1 )
  local rt; rt=$(echo "$out" | grep -oE "real [0-9.]+" | awk '{print $2}')
  local res; res=$(echo "$out" | grep -oE "^(sat|unsat|unknown)$" | head -1)
  if [[ -z "$res" || "$res" == "unknown" ]]; then
    echo "T/O"
  else
    echo "$rt"
  fi
}

cat > "$OUTPUT_TSV" <<HEADER
# Bitwuzla 0.9.0-dev and cvc5 1.3.3 on Martin's 210-benchmark sample
# 10 s timeout; T/O denotes timeout or unknown
# Used to validate the "wins beyond all current solvers" claim
benchmark	bitwuzla	cvc5
HEADER

n=0
total=$(grep -vc '^#\|^benchmark' "$INPUT_TSV")
echo "Running $total benchmarks against Bitwuzla and cvc5..." >&2
echo "Estimated max wall: $((total * TIMEOUT * 2 / 60)) minutes" >&2

while IFS=$'\t' read -r name rest; do
  case "$name" in '#'*|'') continue ;; benchmark) continue ;; esac
  file=$(benchmark_path "$name")
  if [[ ! -f "$file" ]]; then
    echo "MISSING	$name" >&2
    printf '%s\tMISSING\tMISSING\n' "$name" >> "$OUTPUT_TSV"
    continue
  fi
  bw=$(run_solver bitwuzla "$file")
  cv=$(run_solver cvc5 "$file")
  printf '%s\t%s\t%s\n' "$name" "$bw" "$cv" >> "$OUTPUT_TSV"
  n=$((n+1))
  if (( n % 20 == 0 )); then
    echo "  $n / $total" >&2
  fi
done < "$INPUT_TSV"

echo "Done. Output: $OUTPUT_TSV ($n rows)" >&2
