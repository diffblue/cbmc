#!/bin/bash
# Run 5-approach comparison on Martin's subpolynomial-encoding benchmarks.
# Stratified sample: pick a small number per (degree, bitwidth, category).
set -u
ROOT=$(realpath "$(dirname "$0")/..")
cd "$ROOT"
SMT2=$ROOT/build/bin/smt2_solver
TIMEOUT=10
MARTIN_DIR=/tmp/martin-bench
OUTFILE=$ROOT/bench-multiplication/martin-subpoly-comparison.tsv

ulimit -v 57591731 2>/dev/null || true

if [ ! -d "$MARTIN_DIR/seed-23" ]; then
  mkdir -p "$MARTIN_DIR"
  cd "$MARTIN_DIR"
  tar -xJf /tmp/subpolynomial-encoding/benchmarks/seed-23.tar.xz
  tar -xJf /tmp/subpolynomial-encoding/benchmarks/seed-42.tar.xz
  cd "$ROOT"
fi

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
# Stratified sample: 5 per (bw, degree-bucket, category)
# Time in seconds; T/O = ${TIMEOUT} s
benchmark	shift_add	comba_cs	pair_detect	p2_algebraic	all_combined
HEADER

# Stratified sample: 3 categories that are interesting (addition, multiplication, correctness)
# × 3 bw (8, 16, 32) × 4 degree buckets (low: 2-5, mid: 8-12, high: 18-22, very high: 28-32)
# × 2 seeds = 72 strata, 2 samples each = ~144 benchmarks
BENCHMARKS=()
for seed in seed-23 seed-42; do
  for bw in 8 16 32; do
    for degbucket in "2 3 4 5" "8 9 10 12" "18 20 22" "28 30 32"; do
      for cat in "addition-original-native-encoding" \
                 "multiplication-original-native-encoding" \
                 "correctness-original-native-encoding-vs-original-subpolynomial-encoding"; do
        # pick 2 random degrees from bucket
        for deg in $(echo $degbucket | tr ' ' '\n' | shuf -n 2); do
          f="$MARTIN_DIR/$seed/bitwidth-${bw}-degree-${deg}-${seed}-${cat}.smt2"
          [ -f "$f" ] && BENCHMARKS+=("$f")
        done
      done
    done
  done
done

echo "Will run ${#BENCHMARKS[@]} benchmarks × 5 configs × ${TIMEOUT}s timeout" >&2
i=0
for test in "${BENCHMARKS[@]}"; do
  i=$((i+1))
  name=$(basename "$test" .smt2)
  printf "[%3d/%d] %-90s " "$i" "${#BENCHMARKS[@]}" "${name:0:89}" >&2
  sa=$(run_cell "$test" shift_add)
  cs=$(run_cell "$test" comba_cs)
  pd=$(run_cell "$test" pair_detect)
  p2=$(run_cell "$test" p2_algebraic)
  ac=$(run_cell "$test" all_combined)
  echo "$sa $cs $pd $p2 $ac" >&2
  printf "%-90s\t%s\t%s\t%s\t%s\t%s\n" "$name" "$sa" "$cs" "$pd" "$p2" "$ac" >> "$OUTFILE"
done

echo "Saved to $OUTFILE" >&2
