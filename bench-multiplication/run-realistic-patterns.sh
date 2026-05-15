#!/bin/bash
# Realistic patterns A/B comparison.
# Output: bench-multiplication/realistic-patterns/results.tsv
set -u
ROOT=$(realpath "$(dirname "$0")/..")
cd "$ROOT"
CBMC=$ROOT/build/bin/cbmc
DEFAULT_TIMEOUT=60
OUTFILE=$ROOT/bench-multiplication/realistic-patterns/results.tsv

ulimit -v 57591731 2>/dev/null || true

cat > "$OUTFILE" <<HEADER
# Realistic patterns: pair detection A/B
# Time in seconds; T/O = ${DEFAULT_TIMEOUT} s timeout (300 s for p1)
pattern	with_s	with_pairs	with_dist	without_s	speedup	notes
HEADER

run_one_pattern() {
  local f=$1
  local timeout=${2:-$DEFAULT_TIMEOUT}
  local notes=$3
  
  local name
  name=$(basename "$f" .c)
  
  local rt_w
  rt_w=$( { time -p timeout $timeout "$CBMC" "$f" --refine-arithmetic --no-standard-checks >/tmp/rp.log 2>&1; } 2>&1 | grep -oE "real [0-9.]+" | awk '{print $2}')
  local ver_w
  ver_w=$(grep -oE "VERIFICATION SUCCESSFUL|VERIFICATION FAILED" /tmp/rp.log | head -1)
  local pairs
  pairs=$(grep -oE "[0-9]+ commutative/associative" /tmp/rp.log | grep -oE "[0-9]+" | head -1)
  local dist
  dist=$(grep -oE "[0-9]+ distributive" /tmp/rp.log | grep -oE "[0-9]+" | head -1)
  
  local rt_n
  rt_n=$( { time -p timeout $timeout env CBMC_DISABLE_REFINE_PAIR_DETECTION=1 "$CBMC" "$f" --refine-arithmetic --no-standard-checks >/tmp/rp2.log 2>&1; } 2>&1 | grep -oE "real [0-9.]+" | awk '{print $2}')
  local ver_n
  ver_n=$(grep -oE "VERIFICATION SUCCESSFUL|VERIFICATION FAILED" /tmp/rp2.log | head -1)
  
  [ -z "$ver_w" ] && rt_w="T/O"
  [ -z "$ver_n" ] && rt_n="T/O"
  
  local sp
  if [[ "$rt_w" == "T/O" || "$rt_n" == "T/O" ]]; then sp="-"
  else sp=$(echo "scale=1; $rt_n / $rt_w" | bc 2>/dev/null); sp="${sp}x"; fi
  
  echo -e "${name}\t${rt_w}\t${pairs:-0}\t${dist:-0}\t${rt_n}\t${sp}\t${notes}" | tee -a "$OUTFILE"
}

run_one_pattern bench-multiplication/realistic-patterns/p1_modmul_comm.c 300 "modular reduction dominates"
run_one_pattern bench-multiplication/realistic-patterns/p2_crc_chain.c 60 "no pair detected (XOR-based chain)"
run_one_pattern bench-multiplication/realistic-patterns/p3_pixel_index.c 60 "commutative pair"
run_one_pattern bench-multiplication/realistic-patterns/p4_dot_product.c 60 "3 pairs detected"
run_one_pattern bench-multiplication/realistic-patterns/p5_polynomial.c 60 "nested mults, BV resolution gap"
run_one_pattern bench-multiplication/realistic-patterns/p6_overflow_pair.c 60 "trivially fast"
run_one_pattern bench-multiplication/realistic-patterns/p7_bitmix_distrib.c 60 "distributivity through stored sum"
run_one_pattern bench-multiplication/realistic-patterns/p8_buffer_offset.c 60 "associativity"

echo "Saved to $OUTFILE"
