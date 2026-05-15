#!/bin/bash
# SMT2 wide comparison v2: now includes pair_detect and all_combined
# columns (smt2_solver --refine-arithmetic was added).
set -u
ROOT=$(realpath "$(dirname "$0")/..")
cd "$ROOT"
SMT2=$ROOT/build/bin/smt2_solver
TIMEOUT=15
OUTFILE=$ROOT/bench-multiplication/wide-smt2-five-approach.tsv

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
# SMT2 wide comparison (v2): all five configurations
# Time in seconds; T/O = ${TIMEOUT} s
benchmark	shift_add	comba_cs	pair_detect	p2_algebraic	all_combined
HEADER

# Build benchmark list
BENCHMARKS=()
for b in $(awk 'NR>1 && $2=="cbmc" {print $1}' doc/paper-algebraic/data/paper2-suite-results.tsv | sort -u); do
  f=$ROOT/bench-multiplication/smt-comp/${b}.smt2
  [ -f "$f" ] && BENCHMARKS+=("$f")
done
for f in $ROOT/bench-multiplication/degree-scaling/*.smt2; do
  [ -f "$f" ] && BENCHMARKS+=("$f")
done
for f in $ROOT/bench-multiplication/variables-scaling/*.smt2; do
  [ -f "$f" ] && BENCHMARKS+=("$f")
done
for f in /tmp/bw_gen/comm_*.smt2 /tmp/bw_gen/assoc_*.smt2; do
  [ -f "$f" ] && BENCHMARKS+=("$f")
done

echo "Will run ${#BENCHMARKS[@]} benchmarks × 5 configs × ${TIMEOUT}s timeout" >&2
i=0
for test in "${BENCHMARKS[@]}"; do
  i=$((i+1))
  name=$(basename "$test" .smt2)
  printf "[%3d/%d] %-50s " "$i" "${#BENCHMARKS[@]}" "$name" >&2
  sa=$(run_cell "$test" shift_add)
  cs=$(run_cell "$test" comba_cs)
  pd=$(run_cell "$test" pair_detect)
  p2=$(run_cell "$test" p2_algebraic)
  ac=$(run_cell "$test" all_combined)
  echo "$sa $cs $pd $p2 $ac" >&2
  printf "%-50s\t%s\t%s\t%s\t%s\t%s\n" "$name" "$sa" "$cs" "$pd" "$p2" "$ac" >> "$OUTFILE"
done

echo "Saved to $OUTFILE" >&2
