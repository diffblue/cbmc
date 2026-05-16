#!/bin/bash
# Item 7 (expression normalisation) ablation on Martin's subpolynomial
# benchmark sample (the same ~210 sample used in
# martin-subpoly-results.md). These benchmarks include cases where
# the algebraic layer returns UNKNOWN; item 7 might catch some.
set -u
ROOT=$(realpath "$(dirname "$0")/..")
cd "$ROOT"
SMT2=$ROOT/build/bin/smt2_solver
TIMEOUT=10
MARTIN_DIR=/tmp/martin-bench
OUTFILE=$ROOT/bench-multiplication/expr-norm-martin-ablation.tsv

ulimit -v 57591731 2>/dev/null || true

run_cell() {
  local test=$1; local cfg=$2
  case $cfg in
    default)   prefix="";;
    expr_norm) prefix="env ENABLE_GB_EXPR_NORMALISE=1";;
  esac
  rt=$( { time -p timeout $TIMEOUT $prefix $SMT2 --cadical "$test" --multiplier-encoding comba-cs >/tmp/r.log 2>&1; } 2>&1 | grep -oE "real [0-9.]+" | awk '{print $2}')
  res=$(grep -oE "^(sat|unsat|unknown)$" /tmp/r.log | head -1)
  if [ -z "$res" ]; then echo "T/O"
  else echo "$rt"; fi
}

cat > "$OUTFILE" <<HEADER
# Item 7 (expression normalisation) ablation on Martin's benchmarks.
# Same stratified random sample as martin-subpoly-results.md.
# Time in seconds; T/O = ${TIMEOUT} s
benchmark	default	expr_norm
HEADER

# Reuse the same sampling strategy as run-martin-subpoly-v2.sh
BENCHMARKS=()
for seed_dir in seed-23 seed-42; do
  if [ ! -d "$MARTIN_DIR/$seed_dir" ]; then continue; fi
  cats=$(ls "$MARTIN_DIR/$seed_dir" | grep '\.smt2$' | sed 's|.*-degree-[0-9]*-seed-[0-9]*-||' | sed 's|\.smt2$||' | sort -u)
  for cat in $cats; do
    files=$(ls "$MARTIN_DIR/$seed_dir/"*"-${cat}.smt2" 2>/dev/null | shuf -n 5)
    for f in $files; do
      BENCHMARKS+=("$f")
    done
  done
done

echo "Will run ${#BENCHMARKS[@]} benchmarks × 2 configs × ${TIMEOUT}s timeout" >&2
i=0
for test in "${BENCHMARKS[@]}"; do
  i=$((i+1))
  name=$(basename "$test" .smt2)
  printf "[%3d/%d] %-100s " "$i" "${#BENCHMARKS[@]}" "${name:0:99}" >&2
  d=$(run_cell "$test" default)
  e=$(run_cell "$test" expr_norm)
  echo "default=$d expr_norm=$e" >&2
  printf "%s\t%s\t%s\n" "$name" "$d" "$e" >> "$OUTFILE"
done

echo "Saved to $OUTFILE" >&2
