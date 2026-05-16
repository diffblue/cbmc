#!/bin/bash
# Item 7 (expression normalisation) ablation on full 39-benchmark suite.
# Two configurations:
# - default: standard pipeline (algebraic layer + bit-blast)
# - expr_norm: default + post-Buchberger expression normalisation (item 7)
#
# Goal: see whether item 7 catches benchmarks the existing pipeline misses,
# or whether it adds overhead without benefit.
set -u
ROOT=$(realpath "$(dirname "$0")/..")
cd "$ROOT"
SMT2=$ROOT/build/bin/smt2_solver
TIMEOUT=30
OUTFILE=$ROOT/bench-multiplication/expr-norm-ablation.tsv

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
# Item 7 (expression normalisation via Gröbner basis) ablation
# default  = standard pipeline (algebraic layer + bit-blast)
# expr_norm= default + post-Buchberger expression normalisation
# Time in seconds; T/O = ${TIMEOUT} s
benchmark	default	expr_norm
HEADER

benchmarks=(
  comm_8 comm_10 comm_11 comm_12 comm_13 comm_14 comm_15 comm_16
  comm_18 comm_20 comm_24 comm_32
  assoc_8 distrib_8
  overflow_detect_16 add_overflow_16 checked_mul_16 add_chain_16 add_chain_32
  add_sub_cancel_16 equiv_unsat_8add_16
  bf16_mul_comm bf16_mul_comm_v2 bf16_mul_const bf16_mul_mono
  strength_chain_16 strength_16_15 strength_16_31
  mul_ineq_12 div_mul_roundtrip_12 gf256_mul_assoc crypto_square_mod
  barrett_red_8 fixedpoint_mul_16
  dsp_image_reject dsp_horner_16 dsp_vanishing_poly_8 dsp_vanishing_mv
  dsp_coeff_scale_8
)

i=0
total=${#benchmarks[@]}
for bench in "${benchmarks[@]}"; do
  i=$((i+1))
  test=$ROOT/bench-multiplication/smt-comp/${bench}.smt2
  printf "[%2d/%d] %-30s " "$i" "$total" "$bench" >&2
  d=$(run_cell "$test" default)
  e=$(run_cell "$test" expr_norm)
  echo "default=$d expr_norm=$e" >&2
  printf "%s\t%s\t%s\n" "$bench" "$d" "$e" >> "$OUTFILE"
done

echo "Saved to $OUTFILE" >&2
