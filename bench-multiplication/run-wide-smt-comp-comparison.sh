#!/bin/bash
# SMT-COMP real-world sample: 66 benchmarks from third-party SMT-COMP
# 2024 submitters (BuchwaldFried, Goel-hwbench, Noetzli, UltimateAutomizer,
# Sage2, VS3, brummayerbiere, calypto, galois, etc.). Extends Paper 2's
# §4.2 evaluation to all 5 configurations now that smt2_solver supports
# --refine-arithmetic.
set -u
ROOT=$(realpath "$(dirname "$0")/..")
cd "$ROOT"
SMT2=$ROOT/build/bin/smt2_solver
TIMEOUT=15
DIR=$ROOT/doc/paper-bitblasting/data/smt-comp-sample
OUTFILE=$ROOT/bench-multiplication/wide-smt-comp-five-approach.tsv

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
# SMT-COMP 2024 sample: real-world third-party submitters (66 benchmarks)
# Time in seconds; T/O = ${TIMEOUT} s
# Source: doc/paper-bitblasting/data/smt-comp-sample/*.smt2
benchmark	shift_add	comba_cs	pair_detect	p2_algebraic	all_combined
HEADER

i=0
total=$(ls $DIR/*.smt2 | wc -l)
for test in $DIR/*.smt2; do
  i=$((i+1))
  name=$(basename "$test" .smt2)
  printf "[%2d/%d] %-65s " "$i" "$total" "${name:0:64}" >&2
  sa=$(run_cell "$test" shift_add)
  cs=$(run_cell "$test" comba_cs)
  pd=$(run_cell "$test" pair_detect)
  p2=$(run_cell "$test" p2_algebraic)
  ac=$(run_cell "$test" all_combined)
  echo "$sa $cs $pd $p2 $ac" >&2
  printf "%-65s\t%s\t%s\t%s\t%s\t%s\n" "$name" "$sa" "$cs" "$pd" "$p2" "$ac" >> "$OUTFILE"
done

echo "Saved to $OUTFILE" >&2
