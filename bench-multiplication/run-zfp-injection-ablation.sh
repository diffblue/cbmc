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

# 39-benchmark custom suite (from Paper 2 Table 1)
benchmarks=(
  comm_8 comm_16 comm_24 comm_32
  assoc_8 assoc_16 assoc_32
  distrib_8 distrib_16 distrib_32
  overflow_detect_16 add_overflow_16 mul_no_overflow_16 mul_ineq_12
  swap_xor3_16
  dsp_image_reject dsp_image_reject_inline dsp_horner_8 dsp_horner_16
  dsp_vanishing_8 dsp_vanishing_poly_8 dsp_vanishing_mv dsp_coeff_scale_8 dsp_mac_comm_16
  div_test_8 div_roundtrip_8 mod_basic_8 div_simple_4
  bf16_mul_comm bf16_mul_comm_v2 bf16_mul_assoc bf16_mul_assoc_v2
  bf16_mul_zero bf16_neg_zero bf16_signed_zero bf16_inf_handling bf16_nan_check bf16_subnormal
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
