#!/bin/bash
# Run on seed-42 only, append to existing TSV
set -u
ROOT=$(realpath "$(dirname "$0")/..")
cd "$ROOT"
SMT2=$ROOT/build/bin/smt2_solver
TIMEOUT=10
MARTIN_DIR=/tmp/martin-bench
OUTFILE=$ROOT/bench-multiplication/martin-subpoly-comparison.tsv

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

# seed-42 sample with same stratification
BENCHMARKS=()
seed=seed-42
for bw in 8 16 32; do
  for degbucket in "2 3 4 5" "8 9 10 12" "18 20 22" "28 30 32"; do
    for cat in "addition-original-native-encoding" \
               "multiplication-original-native-encoding" \
               "correctness-original-native-encoding-vs-original-subpolynomial-encoding"; do
      for deg in $(echo $degbucket | tr ' ' '\n' | shuf -n 2); do
        f="$MARTIN_DIR/$seed/bitwidth-${bw}-degree-${deg}-${seed}-${cat}.smt2"
        [ -f "$f" ] && BENCHMARKS+=("$f")
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
  printf "%s\t%s\t%s\t%s\t%s\t%s\n" "$name" "$sa" "$cs" "$pd" "$p2" "$ac" >> "$OUTFILE"
done

echo "Saved to $OUTFILE" >&2
