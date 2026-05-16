#!/bin/bash
# Stratified random sample from BOTH seeds, all categories
set -u
ROOT=$(realpath "$(dirname "$0")/..")
cd "$ROOT"
SMT2=$ROOT/build/bin/smt2_solver
TIMEOUT=10
MARTIN_DIR=/tmp/martin-bench
OUTFILE=$ROOT/bench-multiplication/martin-subpoly-comparison-v2.tsv

ulimit -v 57591731 2>/dev/null || true

run_cell() {
  local test=$1; local mode=$2
  local prefix=""; local extra=""
  case $mode in
    shift_add)
      prefix="env DISABLE_SIMPLIFY=1 DISABLE_ALGEBRAIC=1"
      extra="--multiplier-encoding shift-add" ;;
    comba_cs)
      prefix="env DISABLE_SIMPLIFY=1 DISABLE_ALGEBRAIC=1"
      extra="--multiplier-encoding comba-cs" ;;
    pair_detect)
      prefix="env DISABLE_SIMPLIFY=1 DISABLE_ALGEBRAIC=1"
      extra="--refine-arithmetic --multiplier-encoding comba-cs" ;;
    p2_algebraic)
      prefix=""
      extra="--multiplier-encoding comba-cs" ;;
    all_combined)
      prefix=""
      extra="--refine-arithmetic --multiplier-encoding comba-cs" ;;
  esac
  rt=$( { time -p timeout $TIMEOUT $prefix $SMT2 --cadical "$test" $extra >/tmp/c.log 2>&1; } 2>&1 | grep -oE "real [0-9.]+" | awk '{print $2}')
  res=$(grep -oE "^(sat|unsat|unknown)$" /tmp/c.log | head -1)
  if [ -z "$res" ]; then echo "T/O"
  else echo "$rt"; fi
}

cat > "$OUTFILE" <<HEADER
# Martin's subpolynomial-encoding benchmarks (random poly identities)
# Source: github.com/martin-cs/subpolynomial-encoding
# Stratified random sample (both seeds, all categories)
# Time in seconds; T/O = ${TIMEOUT} s
benchmark	shift_add	comba_cs	pair_detect	p2_algebraic	all_combined
HEADER

# Sample N benchmarks from each seed/category combination
# 2 per (seed, category) covering many degrees/bw
BENCHMARKS=()
for seed_dir in seed-23 seed-42; do
  if [ ! -d "$MARTIN_DIR/$seed_dir" ]; then continue; fi
  # Get list of categories present
  cats=$(ls "$MARTIN_DIR/$seed_dir" | grep '\.smt2$' | sed 's|.*-degree-[0-9]*-seed-[0-9]*-||' | sed 's|\.smt2$||' | sort -u)
  for cat in $cats; do
    # Pick 5 random samples from this seed × category
    files=$(ls "$MARTIN_DIR/$seed_dir/"*"-${cat}.smt2" 2>/dev/null | shuf -n 5)
    for f in $files; do
      BENCHMARKS+=("$f")
    done
  done
done

echo "Will run ${#BENCHMARKS[@]} benchmarks × 5 configs × ${TIMEOUT}s timeout" >&2
i=0
for test in "${BENCHMARKS[@]}"; do
  i=$((i+1))
  name=$(basename "$test" .smt2)
  seed=$(echo "$test" | grep -oE "seed-[0-9]+" | head -1)
  printf "[%3d/%d] %-100s " "$i" "${#BENCHMARKS[@]}" "${name:0:99}" >&2
  sa=$(run_cell "$test" shift_add)
  cs=$(run_cell "$test" comba_cs)
  pd=$(run_cell "$test" pair_detect)
  p2=$(run_cell "$test" p2_algebraic)
  ac=$(run_cell "$test" all_combined)
  echo "$sa $cs $pd $p2 $ac" >&2
  printf "%s\t%s\t%s\t%s\t%s\t%s\n" "$name" "$sa" "$cs" "$pd" "$p2" "$ac" >> "$OUTFILE"
done

echo "Saved to $OUTFILE" >&2
