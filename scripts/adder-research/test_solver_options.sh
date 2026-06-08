#!/bin/bash
# Test the effect of solver configuration options on adder benchmarks.
# Varies CaDiCaL preprocessing/inprocessing options and MiniSat settings.
#
# Usage: test_solver_options.sh <cnf_file> [timeout]

set -e
CBMC_DIR=$(cd "$(dirname "$0")/../.." && pwd)
CADICAL=$CBMC_DIR/build/cadical-src/build/cadical
CNF=$1
TIMEOUT=${2:-60}

if [ -z "$CNF" ]; then
  echo "Usage: $0 <cnf_file> [timeout]"
  exit 1
fi

echo "=== Solver Options Experiment ==="
echo "Input: $(head -1 $CNF)"
echo ""

run_cadical() {
  local label=$1
  shift
  local out=$(ulimit -v 8000000; timeout $TIMEOUT $CADICAL "$CNF" "$@" 2>&1)
  local time=$(echo "$out" | grep "total process time" | sed 's/.*: *//;s/ .*//')
  local conflicts=$(echo "$out" | grep "^c conflicts:" | sed 's/.*: *\([0-9]*\).*/\1/')
  local elim=$(echo "$out" | grep "^c eliminated:" | sed 's/.*\b\([0-9.]*\) %.*/\1/')
  local props=$(echo "$out" | grep "^c propagations:" | sed 's/.*: *\([0-9]*\).*/\1/')
  [ -z "$time" ] && time="T/O"
  printf "%-40s time=%-8s conflicts=%-8s elim=%-6s props=%s\n" \
    "$label" "$time" "$conflicts" "${elim}%" "$props"
}

echo "--- CaDiCaL: Preprocessing variations ---"
run_cadical "Default"
run_cadical "No preprocessing"          --no-elim --no-subsume --no-vivify --no-sweep --no-backbone --no-congruence
run_cadical "No BVE only"               --no-elim
run_cadical "No subsumption only"        --no-subsume
run_cadical "No vivification only"       --no-vivify
run_cadical "No sweep only"              --no-sweep
run_cadical "No congruence only"         --no-congruence
run_cadical "No backbone only"           --no-backbone

echo ""
echo "--- CaDiCaL: Search strategy variations ---"
run_cadical "Default (focused+stable)"
run_cadical "Always focused"             --no-stabilize
run_cadical "Always stable"              --stabilizeonly=true
run_cadical "No restarts"                --no-restart
run_cadical "No chronological BT"        --no-chrono
run_cadical "No inprocessing"            --no-inprocessing

echo ""
echo "--- CaDiCaL: Phase saving variations ---"
run_cadical "Default phase"
run_cadical "Always positive"            --phase=true
run_cadical "Always negative"            --phase=false

echo ""
echo "--- CBMC MiniSat variations ---"
# MiniSat has fewer options, but we can test via CBMC flags
run_cbmc() {
  local label=$1
  shift
  local out=$(ulimit -v 8000000; timeout $TIMEOUT \
    $CBMC_DIR/build/bin/cbmc "$@" 2>&1)
  local time=$(echo "$out" | grep "^Runtime Solver:" | tail -1 | sed 's/Runtime Solver: //')
  local vars=$(echo "$out" | grep "variables, " | tail -1 | sed 's/.*\b\([0-9]*\) variables,.*/\1/')
  [ -z "$time" ] && time="T/O"
  printf "%-40s time=%-8s vars=%s\n" "$label" "$time" "$vars"
}

# Find the benchmark C file that generated this CNF
# (We need to re-run CBMC for MiniSat tests)
for bench in scripts/adder-research/micro_benchmarks/*.c; do
  bname=$(basename "$bench" .c)
  echo ""
  echo "--- MiniSat on $bname ---"
  run_cbmc "MiniSat default" "$bench" --unwind 201 --no-unwinding-assertions --verbosity 8 --sat-solver minisat2
  break  # Just test the first benchmark as a sample
done
