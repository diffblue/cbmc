#!/bin/bash
# CBMC auto-large benchmarks A/B.
# Output: bench-multiplication/auto-large-results.tsv
set -u
ROOT=$(realpath "$(dirname "$0")/..")
cd "$ROOT"
CBMC=$ROOT/build/bin/cbmc
TIMEOUT=60
OUTFILE=$ROOT/bench-multiplication/auto-large-results.tsv

ulimit -v 57591731 2>/dev/null || true

# Generate the auto-large benchmarks in /tmp.
mkdir -p /tmp/auto-large
timeout 30 python3 -c "
from pathlib import Path
import sys
sys.path.insert(0, '$ROOT/scripts')
from profiling.benchmarks import generate_auto_large_benchmarks
generate_auto_large_benchmarks(Path('/tmp/auto-large'))
" >/dev/null 2>&1

declare -A BENCH=(
  [linked_list]="--bounds-check --pointer-check --unwind 200"
  [array_ops]="--bounds-check --unwind 55"
  [structs]="--bounds-check --pointer-check --unwind 10"
  [dlinked_list]="--bounds-check --pointer-check --unwind 150"
  [string_ops]="--bounds-check --pointer-check --unwind 25"
  [func_ptrs]="--bounds-check --pointer-check --unwind 15"
  [bitvector]="--bounds-check --unwind 40"
  [matrix]="--bounds-check --unwind 12"
  [unions]="--bounds-check --pointer-check --unwind 10"
  [tree]="--bounds-check --pointer-check --unwind 8"
)

cat > "$OUTFILE" <<HEADER
# CBMC's profile_cbmc auto-large benchmarks with --refine-arithmetic
# Time in seconds; T/O = ${TIMEOUT} s timeout
benchmark	with_s	with_pairs	without_s
HEADER

for name in "${!BENCH[@]}"; do
  args=${BENCH[$name]}
  file=/tmp/auto-large/benchmarks/${name}.c
  [ -f "$file" ] || continue
  
  rt_w=$( { time -p timeout $TIMEOUT $CBMC $file $args --refine-arithmetic >/tmp/al.log 2>&1; } 2>&1 | grep -oE "real [0-9.]+" | awk '{print $2}')
  pairs=$(grep -oE "[0-9]+ commutative" /tmp/al.log | grep -oE "[0-9]+" | head -1)
  ver_w=$(grep -oE "VERIFICATION SUCCESSFUL|VERIFICATION FAILED" /tmp/al.log | head -1)
  
  rt_n=$( { time -p timeout $TIMEOUT env CBMC_DISABLE_REFINE_PAIR_DETECTION=1 $CBMC $file $args --refine-arithmetic >/tmp/al2.log 2>&1; } 2>&1 | grep -oE "real [0-9.]+" | awk '{print $2}')
  ver_n=$(grep -oE "VERIFICATION SUCCESSFUL|VERIFICATION FAILED" /tmp/al2.log | head -1)
  
  [ -z "$ver_w" ] && rt_w="T/O"
  [ -z "$ver_n" ] && rt_n="T/O"
  
  echo -e "${name}\t${rt_w}\t${pairs:-0}\t${rt_n}" | tee -a "$OUTFILE"
done
echo "Saved to $OUTFILE"
