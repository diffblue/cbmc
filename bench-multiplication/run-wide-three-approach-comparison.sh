#!/bin/bash
# Wide three-approach comparison across all available C benchmarks:
# bench-multiplication/*.c (excluding fp_*), realistic-patterns/*.c,
# and synthetic stored patterns. Five configurations as before.
set -u
ROOT=$(realpath "$(dirname "$0")/..")
cd "$ROOT"
CBMC=$ROOT/build/bin/cbmc
TIMEOUT=15
OUTFILE=$ROOT/bench-multiplication/wide-three-approach-comparison.tsv

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
  rt=$( { time -p timeout $TIMEOUT $prefix $CBMC $test --no-standard-checks $extra >/tmp/c.log 2>&1; } 2>&1 | grep -oE "real [0-9.]+" | awk '{print $2}')
  ver=$(grep -oE "VERIFICATION SUCCESSFUL|VERIFICATION FAILED" /tmp/c.log | head -1)
  if [ -z "$ver" ]; then echo "T/O"
  else echo "$rt"; fi
}

# Header
cat > "$OUTFILE" <<HEADER
# Wide three-approach comparison
# Time in seconds; T/O = ${TIMEOUT} s
# shift_add:    DISABLE_ALGEBRAIC + shift-add
# comba_cs:     DISABLE_ALGEBRAIC + comba-cs (Paper 1)
# pair_detect:  DISABLE_ALGEBRAIC + --refine-arithmetic + comba-cs (Beame-Liew-inspired)
# p2_algebraic: algebraic + comba-cs (Paper 2)
# all_combined: algebraic + --refine-arithmetic + comba-cs (now optimised)
benchmark	shift_add	comba_cs	pair_detect	p2_algebraic	all_combined
HEADER

# Build the benchmark list
BENCHMARKS=()
# bench-multiplication/*.c excluding floating point and pair-detection-suite
for f in $ROOT/bench-multiplication/*.c; do
  case "$(basename $f)" in
    fp_*) continue ;;
  esac
  BENCHMARKS+=("$f")
done
# realistic-patterns
for f in $ROOT/bench-multiplication/realistic-patterns/p*.c; do
  BENCHMARKS+=("$f")
done
# synthetic stored
for f in /tmp/stored_comm.c /tmp/stored_comm32.c /tmp/sub_comm.c \
         /tmp/assoc_stored.c /tmp/distrib_simple.c \
         /tmp/bit_level_comm.c /tmp/comm_check.c /tmp/varscale_c.c \
         /tmp/b1_modular.c /tmp/b3_index.c /tmp/b4_polynomial.c \
         /tmp/b5_three_way.c /tmp/b7_three_term.c; do
  if [ -f "$f" ]; then BENCHMARKS+=("$f"); fi
done

echo "Will run ${#BENCHMARKS[@]} benchmarks × 5 configs × ${TIMEOUT}s timeout"
i=0
for test in "${BENCHMARKS[@]}"; do
  i=$((i+1))
  name=$(basename "$test" .c)
  printf "[%3d/%d] %-30s " "$i" "${#BENCHMARKS[@]}" "$name" >&2
  sa=$(run_cell "$test" shift_add)
  cs=$(run_cell "$test" comba_cs)
  pd=$(run_cell "$test" pair_detect)
  p2=$(run_cell "$test" p2_algebraic)
  ac=$(run_cell "$test" all_combined)
  echo "$sa $cs $pd $p2 $ac" >&2
  printf "%-30s\t%s\t%s\t%s\t%s\t%s\n" "$name" "$sa" "$cs" "$pd" "$p2" "$ac" >> "$OUTFILE"
done

echo "Saved to $OUTFILE"
