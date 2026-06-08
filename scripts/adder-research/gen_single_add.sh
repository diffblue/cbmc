#!/bin/bash
# Generate DIMACS for a single addition with a specific encoding.
# Usage: gen_single_add.sh <encoding> <benchmark> <output.cnf>
#
# Encodings: pc, rani, lookahead, kogge, brent, sklansky
# Benchmarks: sat_overflow, unsat_nooverflow, sat_subtract, unsat_equiv

set -e
CBMC_DIR=$(cd "$(dirname "$0")/../.." && pwd)
SRC=$CBMC_DIR/src/solvers/flattening/bv_utils.cpp
ENCODING=$1
BENCH=$2
OUTPUT=$3

if [ -z "$OUTPUT" ]; then
  echo "Usage: $0 <encoding> <benchmark> <output.cnf>"
  echo "Encodings: pc rani lookahead kogge brent sklansky"
  echo "Benchmarks: sat_overflow unsat_nooverflow sat_subtract unsat_equiv"
  exit 1
fi

# Map encoding to implementation
case $ENCODING in
  pc)        IMPL="optimized_ripple_carry_adder" ; EXTRA="" ;;
  rani)      IMPL="simple_ripple_carry_adder"    ; EXTRA="s/^#if 1/#if 0/" ;;
  lookahead) IMPL="carry_lookahead_adder"        ; EXTRA="" ;;
  kogge)     IMPL="kogge_stone_adder"            ; EXTRA="" ;;
  brent)     IMPL="brent_kung_adder"             ; EXTRA="" ;;
  sklansky)  IMPL="sklansky_adder"               ; EXTRA="" ;;
  *) echo "Unknown encoding: $ENCODING"; exit 1 ;;
esac

# Map benchmark to C file
BENCH_DIR=$(dirname "$0")/micro_benchmarks
case $BENCH in
  sat_overflow)     CFILE=$BENCH_DIR/sat_overflow.c ;;
  unsat_nooverflow) CFILE=$BENCH_DIR/unsat_nooverflow.c ;;
  sat_subtract)     CFILE=$BENCH_DIR/sat_subtract.c ;;
  unsat_equiv)      CFILE=$BENCH_DIR/unsat_equiv.c ;;
  *) echo "Unknown benchmark: $BENCH"; exit 1 ;;
esac

# Patch, build, generate DIMACS, restore
cd "$CBMC_DIR"
git checkout -- "$SRC" 2>/dev/null
sed -i "s/return optimized_ripple_carry_adder(op0, op1, std::move(carry_in));/return ${IMPL}(op0, op1, std::move(carry_in));/" "$SRC"
[ -n "$EXTRA" ] && sed -i "$EXTRA" "$SRC"
cmake --build build --target cbmc -- -j$(nproc) 2>&1 | tail -1 >/dev/null
build/bin/cbmc "$CFILE" --unwind 201 --no-unwinding-assertions --dimacs --outfile "$OUTPUT" 2>&1 | tail -1
git checkout -- "$SRC" 2>/dev/null
cmake --build build --target cbmc -- -j$(nproc) 2>&1 | tail -1 >/dev/null
