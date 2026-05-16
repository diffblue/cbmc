#!/bin/bash
# Run the 39-benchmark custom suite with three configurations:
# - default: vanishing test enabled, no ZFP injection (Paper 2 baseline)
# - vanish_off: vanishing test disabled, no ZFP injection (ablation)
# - zfp_only: vanishing test disabled, ZFP injection enabled (Martin's hypothesis)
set -u
ROOT=$(realpath "$(dirname "$0")/..")
cd "$ROOT"
SMT2=$ROOT/build/bin/smt2_solver
TIMEOUT=30
OUTFILE=$ROOT/bench-multiplication/zfp-injection-ablation.tsv

ulimit -v 57591731 2>/dev/null || true

run_cell() {
  local test=$1; local cfg=$2
  case $cfg in
    default)    prefix="";;
    vanish_off) prefix="env DISABLE_VANISHING=1";;
    zfp_only)   prefix="env DISABLE_VANISHING=1 ENABLE_ZFP_INJECTION=1";;
    zfp_plus_van) prefix="env ENABLE_ZFP_INJECTION=1";;
  esac
  rt=$( { time -p timeout $TIMEOUT $prefix $SMT2 --cadical "$test" --multiplier-encoding comba-cs >/tmp/r.log 2>&1; } 2>&1 | grep -oE "real [0-9.]+" | awk '{print $2}')
  res=$(grep -oE "^(sat|unsat|unknown)$" /tmp/r.log | head -1)
  if [ -z "$res" ]; then echo "T/O"
  else echo "$rt"; fi
}

cat > "$OUTFILE" <<HEADER
# 39-benchmark custom suite ablation: vanishing test vs ZFP injection
# default     = vanishing test enabled, no ZFP injection (Paper 2 baseline)
# vanish_off  = vanishing test disabled, no ZFP injection
# zfp_only    = vanishing test disabled, ZFP injection enabled
# zfp_plus_van= both vanishing test and ZFP injection enabled
# Time in seconds; T/O = ${TIMEOUT} s
benchmark	default	vanish_off	zfp_only	zfp_plus_van
HEADER

# 39-benchmark custom suite (canonical list from paper2-suite-results.tsv)
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
  if [ ! -f "$test" ]; then
    printf "[%2d/%d] %-30s SKIPPED (not found)\n" "$i" "$total" "$bench" >&2
    continue
  fi
  printf "[%2d/%d] %-30s " "$i" "$total" "$bench" >&2
  d=$(run_cell "$test" default)
  v=$(run_cell "$test" vanish_off)
  z=$(run_cell "$test" zfp_only)
  zv=$(run_cell "$test" zfp_plus_van)
  echo "default=$d vanish_off=$v zfp_only=$z zfp_plus_van=$zv" >&2
  printf "%s\t%s\t%s\t%s\t%s\n" "$bench" "$d" "$v" "$z" "$zv" >> "$OUTFILE"
done

echo "Saved to $OUTFILE" >&2
