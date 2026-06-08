#!/bin/bash
# Three-approach comparison: Paper 1 best (comba-cs), Beame-Liew-inspired
# pair detection (algebraic-pair), Paper 2 algebraic (Gröbner+vanishing),
# plus baselines (shift-add only, all combined).
set -u
ROOT=$(realpath "$(dirname "$0")/..")
cd "$ROOT"
CBMC=$ROOT/build/bin/cbmc
TIMEOUT=15
OUTFILE=$ROOT/bench-multiplication/three-approach-comparison.tsv

ulimit -v 57591731 2>/dev/null || true

run_cell() {
  local test=$1; local mode=$2
  local prefix=""; local extra=""
  case $mode in
    shift_add)
      prefix="env DISABLE_SIMPLIFY=1 DISABLE_ALGEBRAIC=1"
      extra="--multiplier-encoding shift-add" ;;
    comba_cs)
      # Paper 1: best bit-blast encoding, no algebra, no refinement.
      prefix="env DISABLE_SIMPLIFY=1 DISABLE_ALGEBRAIC=1"
      extra="--multiplier-encoding comba-cs" ;;
    pair_detect)
      # Beame-Liew-inspired pair detection in --refine-arithmetic.
      prefix="env DISABLE_SIMPLIFY=1 DISABLE_ALGEBRAIC=1"
      extra="--refine-arithmetic --multiplier-encoding comba-cs" ;;
    p2_algebraic)
      # Paper 2: full algebraic (Gröbner + vanishing); algebraic stays
      # on but no refinement; comba-cs as bit-blast fallback.
      prefix=""
      extra="--multiplier-encoding comba-cs" ;;
    all_combined)
      # Everything enabled.
      prefix=""
      extra="--refine-arithmetic --multiplier-encoding comba-cs" ;;
  esac
  rt=$( { time -p timeout $TIMEOUT $prefix $CBMC $test --no-standard-checks $extra >/tmp/c.log 2>&1; } 2>&1 | grep -oE "real [0-9.]+" | awk '{print $2}')
  ver=$(grep -oE "VERIFICATION SUCCESSFUL|VERIFICATION FAILED" /tmp/c.log | head -1)
  if [ -z "$ver" ]; then echo "T/O"
  else echo "$rt"; fi
}

cat > "$OUTFILE" <<HEADER
# Three-approach comparison: Paper 1 (comba-cs), pair detection
# (Beame-Liew-inspired), Paper 2 (algebraic).
# Time in seconds; T/O = ${TIMEOUT} s.
# Configurations:
#   shift_add:    DISABLE_ALGEBRAIC + shift-add encoding (baseline)
#   comba_cs:     DISABLE_ALGEBRAIC + comba-cs (Paper 1 best encoding)
#   pair_detect:  DISABLE_ALGEBRAIC + --refine-arithmetic + comba-cs
#                 (Beame-Liew-inspired pair detection only)
#   p2_algebraic: algebraic enabled + comba-cs (Paper 2)
#   all_combined: algebraic + --refine-arithmetic + comba-cs
benchmark	shift_add	comba_cs	pair_detect	p2_algebraic	all_combined
HEADER

# C benchmarks (must use cbmc binary, not smt2_solver)
for test in /tmp/stored_comm.c /tmp/stored_comm32.c /tmp/sub_comm.c /tmp/assoc_stored.c \
            /tmp/distrib_simple.c /tmp/bit_level_comm.c \
            bench-multiplication/realistic-patterns/p1_modmul_comm.c \
            bench-multiplication/realistic-patterns/p3_pixel_index.c \
            bench-multiplication/realistic-patterns/p4_dot_product.c \
            bench-multiplication/realistic-patterns/p7_bitmix_distrib.c \
            bench-multiplication/realistic-patterns/p8_buffer_offset.c \
            /tmp/comm_check.c /tmp/varscale_c.c; do
  [ -f "$test" ] || continue
  name=$(basename "$test" .c)
  sa=$(run_cell "$test" shift_add)
  cs=$(run_cell "$test" comba_cs)
  pd=$(run_cell "$test" pair_detect)
  p2=$(run_cell "$test" p2_algebraic)
  all=$(run_cell "$test" all_combined)
  printf "%-25s\t%s\t%s\t%s\t%s\t%s\n" "$name" "$sa" "$cs" "$pd" "$p2" "$all" | tee -a "$OUTFILE"
done

echo "Saved to $OUTFILE"
