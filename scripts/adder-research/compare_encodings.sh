#!/bin/bash
# Compare all encodings on all micro-benchmarks with multiple solvers.
# Outputs a CSV-format table.
# Usage: compare_encodings.sh [timeout_seconds]

set -e
CBMC_DIR=$(cd "$(dirname "$0")/../.." && pwd)
SRC=$CBMC_DIR/src/solvers/flattening/bv_utils.cpp
CADICAL=$CBMC_DIR/build/cadical-src/build/cadical
TIMEOUT=${1:-60}

ENCODINGS="pc rani lookahead kogge brent sklansky"
BENCHMARKS="sat_overflow unsat_nooverflow sat_subtract unsat_equiv"
SOLVERS="minisat2 cadical"

echo "encoding,benchmark,solver,vars,clauses,conflicts,decisions,propagations,eliminated_pct,solver_time,result"

for enc in $ENCODINGS; do
  # Patch source
  cd "$CBMC_DIR"
  git checkout -- "$SRC" 2>/dev/null

  case $enc in
    pc)        IMPL="optimized_ripple_carry_adder" ;;
    rani)      IMPL="simple_ripple_carry_adder"
               sed -i 's/^#if 1/#if 0/' "$SRC" ;;
    lookahead) IMPL="carry_lookahead_adder" ;;
    kogge)     IMPL="kogge_stone_adder" ;;
    brent)     IMPL="brent_kung_adder" ;;
    sklansky)  IMPL="sklansky_adder" ;;
  esac
  sed -i "s/return optimized_ripple_carry_adder(op0, op1, std::move(carry_in));/return ${IMPL}(op0, op1, std::move(carry_in));/" "$SRC"

  ulimit -v 8000000
  cmake --build build --target cbmc -- -j$(nproc) 2>&1 | tail -1 >/dev/null

  for bench in $BENCHMARKS; do
    CFILE=$(dirname "$0")/micro_benchmarks/${bench}.c

    for solver in $SOLVERS; do
      out=$(ulimit -v 8000000; timeout $TIMEOUT \
        build/bin/cbmc "$CFILE" --unwind 201 --no-unwinding-assertions \
        --verbosity 8 --sat-solver $solver 2>&1)

      vars=$(echo "$out" | grep "variables, " | tail -1 | sed 's/.*\b\([0-9]*\) variables,.*/\1/')
      clauses=$(echo "$out" | grep "variables, " | tail -1 | sed 's/.*variables, \([0-9]*\) clauses.*/\1/')
      stime=$(echo "$out" | grep "^Runtime Solver:" | tail -1 | sed 's/Runtime Solver: //')
      result=$(echo "$out" | grep "SAT checker:" | tail -1 | sed 's/.*instance is //')

      [ -z "$stime" ] && stime="T/O"
      [ -z "$result" ] && result="T/O"
      [ -z "$vars" ] && vars="?"
      [ -z "$clauses" ] && clauses="?"

      echo "$enc,$bench,$solver,$vars,$clauses,,,,,$stime,$result"
    done

    # Also run CaDiCaL standalone for detailed stats
    cnf_tmp=$(mktemp /tmp/adder_XXXXXX.cnf)
    timeout $TIMEOUT build/bin/cbmc "$CFILE" --unwind 201 \
      --no-unwinding-assertions --dimacs --outfile "$cnf_tmp" 2>/dev/null

    if [ -f "$cnf_tmp" ] && [ -s "$cnf_tmp" ]; then
      stats=$(ulimit -v 8000000; timeout $TIMEOUT $CADICAL "$cnf_tmp" 2>&1)
      conflicts=$(echo "$stats" | grep "^c conflicts:" | sed 's/.*: *\([0-9]*\).*/\1/')
      decisions=$(echo "$stats" | grep "^c decisions:" | sed 's/.*: *\([0-9]*\).*/\1/')
      props=$(echo "$stats" | grep "^c propagations:" | sed 's/.*: *\([0-9]*\).*/\1/')
      elim=$(echo "$stats" | grep "^c eliminated:" | sed 's/.*: *\([0-9]*\).*/\1/')
      elim_pct=$(echo "$stats" | grep "^c eliminated:" | sed 's/.*\b\([0-9.]*\) %.*/\1/')
      echo "$enc,$bench,cadical_detail,$vars,$clauses,$conflicts,$decisions,$props,$elim_pct,,"
    fi
    rm -f "$cnf_tmp"
  done
done

# Restore
cd "$CBMC_DIR"
git checkout -- "$SRC" 2>/dev/null
cmake --build build --target cbmc -- -j$(nproc) 2>&1 | tail -1 >/dev/null
