#!/bin/bash
# Benchmark incremental symex modes on aws-c-common proofs.
# Usage: scripts/bench_incremental.sh [cbmc_binary] [aws-c-common_dir]
set -e

CBMC="${1:-build/bin/cbmc}"
GOTO_CC="${CBMC%cbmc}goto-cc"
AWS="${2:-/tmp/aws-c-common}"
RESULTS="/tmp/incremental_bench_results.txt"

if [ ! -x "$CBMC" ]; then echo "cbmc not found: $CBMC"; exit 1; fi
if [ ! -d "$AWS" ]; then echo "aws-c-common not found: $AWS"; exit 1; fi

SRCDIR="$AWS"
PROOF_BASE="$AWS/verification/cbmc"
PROOF_SOURCE="$PROOF_BASE/source"
PROOF_STUB="$PROOF_BASE/stubs"
INCLUDE="-I$AWS/include -I$PROOF_BASE/include -I$AWS"

# Select a subset of proofs (same approach as CI: first 6 per data structure)
PROOFS=$(ls -d "$PROOF_BASE/proofs/aws_"*/ 2>/dev/null | head -18)

compile_proof() {
  local proof_dir="$1"
  local name=$(basename "$proof_dir")
  local harness="$proof_dir/${name}_harness.c"
  local out="/tmp/bench_${name}.gb"

  [ -f "$harness" ] || return 1

  # Gather sources from Makefile
  local sources="$harness"
  local makefile="$proof_dir/Makefile"

  # Add common sources
  for src in "$SRCDIR/source/common.c" "$SRCDIR/source/allocator.c"; do
    [ -f "$src" ] && sources="$sources $src"
  done
  # Add proof helpers
  for src in "$PROOF_SOURCE/make_common_data_structures.c" \
             "$PROOF_SOURCE/utils.c" "$PROOF_STUB/error.c"; do
    [ -f "$src" ] && sources="$sources $src"
  done
  # Add project sources mentioned in Makefile
  for src in $(grep 'PROJECT_SOURCES.*source/' "$makefile" 2>/dev/null | \
               sed 's/.*\$(SRCDIR)//' | sed 's/\s*$//' ); do
    [ -f "$SRCDIR$src" ] && sources="$sources $SRCDIR$src"
  done
  # Add stub sources
  for src in $(grep 'PROOF_STUB.*\.c' "$makefile" 2>/dev/null | \
               sed "s|.*\$(PROOF_STUB)/||" | sed 's/\s*$//'); do
    [ -f "$PROOF_STUB/$src" ] && sources="$sources $PROOF_STUB/$src"
  done

  timeout 30 "$GOTO_CC" $INCLUDE \
    -DCBMC -D__CPROVER \
    --function "${name}_harness" \
    $sources -o "$out" 2>/dev/null && echo "$out"
}

run_cbmc() {
  local gb="$1" mode="$2" extra="$3"
  timeout 60 /usr/bin/time -f "%e" \
    "$CBMC" "$gb" --unwind 10 --unwinding-assertions \
    --no-standard-checks $extra 2>&1
}

printf "%-40s %10s %10s %10s %10s\n" \
  "Proof" "baseline" "periodic" "concurrent" "result" > "$RESULTS"
printf "%-40s %10s %10s %10s %10s\n" \
  "----" "--------" "--------" "----------" "------" >> "$RESULTS"

compiled=0
for proof_dir in $PROOFS; do
  name=$(basename "$proof_dir")
  gb=$(compile_proof "$proof_dir" 2>/dev/null)
  [ -z "$gb" ] && continue
  [ ! -f "$gb" ] && continue
  compiled=$((compiled + 1))

  # Baseline
  out_b=$(run_cbmc "$gb" baseline "" 2>&1)
  time_b=$(echo "$out_b" | tail -1)
  result=$(echo "$out_b" | grep -o 'VERIFICATION [A-Z]*' | head -1)

  # Periodic
  out_p=$(run_cbmc "$gb" periodic "--incremental-check-interval 200" 2>&1)
  time_p=$(echo "$out_p" | tail -1)

  # Concurrent
  out_c=$(run_cbmc "$gb" concurrent \
    "--concurrent-incremental --incremental-check-interval 200" 2>&1)
  time_c=$(echo "$out_c" | tail -1)

  printf "%-40s %10s %10s %10s %10s\n" \
    "$name" "${time_b}s" "${time_p}s" "${time_c}s" "$result" | \
    tee -a "$RESULTS"
done

echo
echo "Compiled $compiled proofs"
echo "Results in $RESULTS"
cat "$RESULTS"
