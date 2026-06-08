#!/bin/bash
# Run the full benchmark suite across all adder encodings.
# Produces one result set per encoding, then a comparison table.
#
# Usage: benchmark_all_encodings.sh [--runs N] [--timeout S] [--xor-gauss]

set -e
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CBMC_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
SRC="$CBMC_DIR/src/solvers/flattening/bv_utils.cpp"
RUNS=3
TIMEOUT=60
XOR_GAUSS=""
REORDER_VARS=""

while [ $# -gt 0 ]; do
  case "$1" in
    --runs) RUNS="$2"; shift 2 ;;
    --timeout) TIMEOUT="$2"; shift 2 ;;
    --xor-gauss) XOR_GAUSS="yes"; shift ;;
    --reorder-vars) REORDER_VARS="yes"; shift ;;
    *) echo "Unknown: $1"; exit 1 ;;
  esac
done

SUFFIX=""
CBMC_FLAGS=""
[ -n "$XOR_GAUSS" ] && SUFFIX="${SUFFIX}_xg" && CBMC_FLAGS="$CBMC_FLAGS --xor-gauss"
[ -n "$REORDER_VARS" ] && SUFFIX="${SUFFIX}_rv" && CBMC_FLAGS="$CBMC_FLAGS --reorder-vars"

ENCODINGS="pc simple rani lookahead"
# Skip parallel prefix — they're proven worse and very slow
# Add them with: ENCODINGS="$ENCODINGS kogge brent sklansky"

build_encoding() {
  local enc=$1
  cd "$CBMC_DIR"
  # Only patch the adder() delegation line, preserving register_xor calls
  # in the individual encoding implementations
  local default_line="return optimized_ripple_carry_adder"
  # First restore just the adder() line to default
  sed -i "s/return .*_adder(op0, op1, std::move(carry_in));/${default_line}(op0, op1, std::move(carry_in));/" "$SRC"

  case $enc in
    pc)        ;; # default
    simple)    sed -i "s/${default_line}/return simple_ripple_carry_adder/" "$SRC" ;;
    rani)      sed -i "s/${default_line}/return simple_ripple_carry_adder/" "$SRC"
               # Toggle the #if to use Rani path
               sed -i '/simple_ripple_carry_adder/,/^}/{s/^#if 1/#if 0/}' "$SRC" ;;
    lookahead) sed -i "s/${default_line}/return carry_lookahead_adder/" "$SRC" ;;
    kogge)     sed -i "s/${default_line}/return kogge_stone_adder/" "$SRC" ;;
    brent)     sed -i "s/${default_line}/return brent_kung_adder/" "$SRC" ;;
    sklansky)  sed -i "s/${default_line}/return sklansky_adder/" "$SRC" ;;
  esac

  ulimit -v 8000000
  cmake --build build --target cbmc smt2_solver -- -j$(nproc) 2>&1 | tail -1
}

echo "=== Benchmarking all encodings (runs=$RUNS, timeout=$TIMEOUT) ==="
echo ""

for enc in $ENCODINGS; do
  config="${enc}${SUFFIX}"
  echo "--- Building $config ---"
  build_encoding "$enc"

  echo "--- Running $config ---"
  ulimit -v 8000000
  bash "$SCRIPT_DIR/run_benchmarks.sh" \
    --runs "$RUNS" \
    --timeout "$TIMEOUT" \
    --config "$config" \
    --solver cadical \
    --cbmc-flags "$CBMC_FLAGS" \
    2>&1 | grep -E "^\[|^  run|^=== Sum|^Bench|^----|^Results"

  echo ""
done

# Restore
cd "$CBMC_DIR"
git checkout -- "$SRC" 2>/dev/null
cmake --build build --target cbmc smt2_solver -- -j$(nproc) 2>&1 | tail -1

# Compare all results
echo "=== Cross-encoding comparison ==="
LATEST_DIR="$SCRIPT_DIR/results"
for enc in $ENCODINGS; do
  config="${enc}${SUFFIX}"
  # Find the most recent result for this config
  result=$(ls -td "$LATEST_DIR"/${config}_* 2>/dev/null | head -1)
  if [ -n "$result" ] && [ -f "$result/results.csv" ]; then
    echo "  $config: $result/results.csv"
  fi
done

echo ""
echo "Use compare_results.sh to compare any two result sets."
