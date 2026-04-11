#!/bin/bash
# Comprehensive benchmark of all adder encoding + solver + option combinations
# Usage: bash run_comprehensive.sh [benchmarks|regression]

set -e
CBMC=/home/ubuntu/cbmc-github.git/build/bin/cbmc
TIMEOUT=120
ULIMIT=6000000
RESULTS_DIR=/home/ubuntu/cbmc-github.git/results
mkdir -p "$RESULTS_DIR"

unset CBMC_XOR_GAUSS

# Benchmarks
declare -A BENCHMARKS
BENCHMARKS[equiv]="scripts/adder-research/benchmarks/synthetic/equiv_unsat_200.c:201"
BENCHMARKS[checksum]="scripts/adder-research/benchmarks/realworld/checksum_200.c:201"
BENCHMARKS[popcount]="scripts/adder-research/benchmarks/realworld/popcount_10.c:331"
BENCHMARKS[byte_ops]="scripts/adder-research/benchmarks/realworld/byte_ops_20.c:21"

# Configurations to test
# Format: "label:solver_flags:env_vars"
CONFIGS=(
  # CaDiCaL configurations
  "cad-ripple:--sat-solver cadical:"
  "cad-BK:--sat-solver cadical --adder-encoding brent-kung:"
  "cad-CLA:--sat-solver cadical --adder-encoding cla:"
  "cad-BK-S0:--sat-solver cadical --adder-encoding brent-kung --reorder-vars 0:"
  "cad-BK-S1:--sat-solver cadical --adder-encoding brent-kung --reorder-vars 1:"
  "cad-BK-S3:--sat-solver cadical --adder-encoding brent-kung --reorder-vars 3:"
  "cad-BK-ph0:--sat-solver cadical --adder-encoding brent-kung --sat-phase 0:"
  "cad-BK-S0-ph0:--sat-solver cadical --adder-encoding brent-kung --reorder-vars 0 --sat-phase 0:"
  "cad-BK-stab0:--sat-solver cadical --adder-encoding brent-kung:CADICAL_OPTS=stabilize=0"
  "cad-BK-S0-ph0-stab0:--sat-solver cadical --adder-encoding brent-kung --reorder-vars 0 --sat-phase 0:CADICAL_OPTS=stabilize=0"
  "cad-rip-stab0:--sat-solver cadical:CADICAL_OPTS=stabilize=0"
  "cad-CLA-stab0:--sat-solver cadical --adder-encoding cla:CADICAL_OPTS=stabilize=0"
  # MiniSat configurations
  "ms-ripple:--sat-solver minisat2:"
  "ms-BK:--sat-solver minisat2 --adder-encoding brent-kung:"
  "ms-CLA:--sat-solver minisat2 --adder-encoding cla:"
  "ms-BK-S0:--sat-solver minisat2 --adder-encoding brent-kung --reorder-vars 0:"
  "ms-BK-S3:--sat-solver minisat2 --adder-encoding brent-kung --reorder-vars 3:"
)

run_benchmark() {
  local label="$1" flags="$2" env_vars="$3" file="$4" unwind="$5" bench_name="$6"
  
  local cmd="ulimit -v $ULIMIT; timeout $TIMEOUT $CBMC $file --unwind $unwind --no-unwinding-assertions --verbosity 8 $flags"
  
  if [ -n "$env_vars" ]; then
    cmd="$env_vars $cmd"
  fi
  
  local t
  t=$(eval "$cmd" 2>&1 | grep "^Runtime Solver:" | tail -1 | sed 's/Runtime Solver: //;s/s$//')
  [ -z "$t" ] && t="T/O"
  echo "$t"
}

run_regression() {
  local label="$1" flags="$2" env_vars="$3"
  
  local cmd="ulimit -v $ULIMIT; cd /home/ubuntu/cbmc-github.git/regression/cbmc && timeout 2400 perl ../test.pl -e -p -c \"$CBMC --validate-goto-model --validate-ssa-equation $flags\" -C -X smt-backend"
  
  if [ -n "$env_vars" ]; then
    cmd="$env_vars $cmd"
  fi
  
  local result
  result=$(eval "$cmd" 2>&1 | grep "tests failed" || echo "TIMEOUT")
  echo "$result"
}

if [ "${1:-benchmarks}" = "benchmarks" ]; then
  echo "=== Performance Benchmarks ==="
  echo ""
  
  # Print header
  printf "%-25s" ""
  for bench in equiv checksum popcount byte_ops; do
    printf " %10s" "$bench"
  done
  echo ""
  
  for config in "${CONFIGS[@]}"; do
    IFS=: read -r label flags env_vars <<< "$config"
    printf "%-25s" "$label"
    
    for bench in equiv checksum popcount byte_ops; do
      IFS=: read -r file unwind <<< "${BENCHMARKS[$bench]}"
      t=$(run_benchmark "$label" "$flags" "$env_vars" "$file" "$unwind" "$bench")
      [ "$t" != "T/O" ] && t=$(printf "%.1f" "$t")
      printf " %10s" "$t"
    done
    echo ""
  done
  
elif [ "$1" = "regression" ]; then
  echo "=== Regression Tests ==="
  echo ""
  
  # Test key configurations
  REG_CONFIGS=(
    "cad-ripple:--sat-solver cadical:"
    "cad-BK:--sat-solver cadical --adder-encoding brent-kung:"
    "cad-CLA:--sat-solver cadical --adder-encoding cla:"
    "ms-ripple:--sat-solver minisat2:"
    "ms-BK:--sat-solver minisat2 --adder-encoding brent-kung:"
    "ms-CLA:--sat-solver minisat2 --adder-encoding cla:"
  )
  
  for config in "${REG_CONFIGS[@]}"; do
    IFS=: read -r label flags env_vars <<< "$config"
    echo -n "  $label: "
    result=$(run_regression "$label" "$flags" "$env_vars")
    echo "$result"
  done
fi
