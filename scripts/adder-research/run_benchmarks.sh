#!/bin/bash
# Reproducible benchmark runner for adder encoding evaluation.
#
# Features:
# - Runs each benchmark multiple times (configurable)
# - Reports mean, stddev, min, max
# - Captures system info for reproducibility
# - Outputs machine-readable CSV + human-readable summary
# - Supports CBMC (C benchmarks) and smt2_solver (SMT2 benchmarks)
# - Memory-limited and time-limited
#
# Usage: run_benchmarks.sh [options]
#   --runs N          Number of runs per benchmark (default: 3)
#   --timeout S       Timeout per run in seconds (default: 120)
#   --memlimit MB     Memory limit in MB (default: 4096)
#   --output DIR      Output directory (default: results/<timestamp>)
#   --config NAME     Configuration name (e.g., "baseline", "xor_gauss")
#   --solver SOLVER   SAT solver: minisat2, cadical (default: cadical)
#   --cbmc PATH       Path to cbmc binary
#   --smt2solver PATH Path to smt2_solver binary
#   --benchdir DIR    Benchmark directory

set -e

# Defaults
RUNS=3
TIMEOUT=120
MEMLIMIT=4096
SOLVER="cadical"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CBMC_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
CBMC="${CBMC:-$CBMC_DIR/build/bin/cbmc}"
SMT2SOLVER="${SMT2SOLVER:-$CBMC_DIR/build/bin/smt2_solver}"
BENCH_DIR="$SCRIPT_DIR/benchmarks"
CONFIG="default"
OUTPUT=""
CBMC_EXTRA_FLAGS=""

# Parse arguments
while [ $# -gt 0 ]; do
  case "$1" in
    --runs)     RUNS="$2"; shift 2 ;;
    --timeout)  TIMEOUT="$2"; shift 2 ;;
    --memlimit) MEMLIMIT="$2"; shift 2 ;;
    --output)   OUTPUT="$2"; shift 2 ;;
    --config)   CONFIG="$2"; shift 2 ;;
    --solver)   SOLVER="$2"; shift 2 ;;
    --cbmc)     CBMC="$2"; shift 2 ;;
    --smt2solver) SMT2SOLVER="$2"; shift 2 ;;
    --benchdir) BENCH_DIR="$2"; shift 2 ;;
    --cbmc-flags) CBMC_EXTRA_FLAGS="$2"; shift 2 ;;
    *) echo "Unknown option: $1"; exit 1 ;;
  esac
done

# Output directory
if [ -z "$OUTPUT" ]; then
  TIMESTAMP=$(date +%Y%m%d_%H%M%S)
  OUTPUT="$SCRIPT_DIR/results/${CONFIG}_${TIMESTAMP}"
fi
mkdir -p "$OUTPUT"

# Fetch benchmarks if needed
bash "$SCRIPT_DIR/fetch_benchmarks.sh" "$BENCH_DIR"

# ============================================================
# System info (for reproducibility)
# ============================================================
cat > "$OUTPUT/system_info.txt" << SYSEOF
Date: $(date -Iseconds)
Hostname: $(hostname)
Kernel: $(uname -r)
CPU: $(grep "model name" /proc/cpuinfo | head -1 | cut -d: -f2 | xargs)
CPU cores: $(nproc)
RAM: $(free -h | awk '/Mem:/{print $2}')
CBMC: $($CBMC --version 2>&1 | head -1)
CBMC path: $(readlink -f "$CBMC")
CBMC git: $(cd "$CBMC_DIR" && git rev-parse --short HEAD 2>/dev/null || echo "unknown")
SAT solver: $SOLVER
Solver versions:
  CaDiCaL: $([ -x "$CBMC_DIR/build/cadical-src/build/cadical" ] && "$CBMC_DIR/build/cadical-src/build/cadical" --version 2>&1 | head -1 || echo "N/A")
  MiniSat: 2.2.1 (CBMC bundled)
  Kissat: $([ -x /tmp/kissat/build/kissat ] && /tmp/kissat/build/kissat --version 2>&1 | head -1 || echo "N/A")
  CryptoMiniSat: $([ -x /tmp/cryptominisat/build/cryptominisat5 ] && /tmp/cryptominisat/build/cryptominisat5 --version 2>&1 | head -1 | sed 's/^c //' || echo "N/A")
  smt2_solver: $([ -x "$SMT2SOLVER" ] && "$SMT2SOLVER" --version 2>&1 | head -1 || echo "N/A")
Config: $CONFIG
Runs per benchmark: $RUNS
Timeout: ${TIMEOUT}s
Memory limit: ${MEMLIMIT}MB
SYSEOF

cat "$OUTPUT/system_info.txt"
echo ""

# ============================================================
# CSV header
# ============================================================
CSV="$OUTPUT/results.csv"
echo "config,benchmark,type,solver,run,vars,clauses,solver_time_s,total_time_s,result,xor_constraints" > "$CSV"

# ============================================================
# Helper: run one benchmark, one iteration
# ============================================================
run_one() {
  local bench_file="$1"
  local bench_name="$2"
  local bench_type="$3"  # "c" or "smt2"
  local run_num="$4"

  local out
  if [ "$bench_type" = "c" ]; then
    # Determine unwind bound from filename or default
    local unwind=201
    case "$bench_name" in
      *_2000*|*_sat_2000*) unwind=2001 ;;
      *_5000*) unwind=5001 ;;
      *_10000*) unwind=10001 ;;
      *_1000*) unwind=1001 ;;
      *_500*) unwind=501 ;;
      *_200*) unwind=201 ;;
      *_100*) unwind=101 ;;
      crc_*) unwind=901 ;;
      hash_combine_*) unwind=51 ;;
      popcount_*) unwind=331 ;;
      *_20*) unwind=21 ;;
      *_10*) unwind=11 ;;
    esac

    out=$(ulimit -v $((MEMLIMIT * 1024)); \
      timeout "$TIMEOUT" "$CBMC" "$bench_file" \
        --unwind "$unwind" --no-unwinding-assertions \
        --verbosity 8 --sat-solver "$SOLVER" $CBMC_EXTRA_FLAGS 2>&1) || true
  elif [ "$bench_type" = "smt2" ]; then
    out=$(ulimit -v $((MEMLIMIT * 1024)); \
      timeout "$TIMEOUT" "$SMT2SOLVER" "$bench_file" 2>&1) || true
  fi

  # Extract metrics
  local vars clauses solver_time total_time result xors
  vars=$(echo "$out" | grep "variables, " | tail -1 | sed 's/.*\b\([0-9]*\) variables,.*/\1/')
  clauses=$(echo "$out" | grep "variables, " | tail -1 | sed 's/.*variables, \([0-9]*\) clauses.*/\1/')
  solver_time=$(echo "$out" | grep "^Runtime Solver:" | tail -1 | sed 's/Runtime Solver: //;s/s$//')
  total_time=$(echo "$out" | grep "^Runtime decision procedure:" | tail -1 | sed 's/Runtime decision procedure: //;s/s$//')
  xors=$(echo "$out" | grep "XOR Gauss propagator:" | sed 's/.*: \([0-9]*\).*/\1/')

  # For smt2_solver, extract from different format
  if [ "$bench_type" = "smt2" ]; then
    vars=$(echo "$out" | grep "variables" | tail -1 | sed 's/.*; \([0-9]*\) variables.*/\1/')
    clauses=$(echo "$out" | grep "clauses" | tail -1 | sed 's/.*\([0-9]*\) clauses.*/\1/')
    solver_time=$(echo "$out" | grep "Runtime" | tail -1 | sed 's/.*: //;s/s$//')
    total_time="$solver_time"
  fi

  # Determine result
  if echo "$out" | grep -q "UNSATISFIABLE\|VERIFICATION SUCCESSFUL"; then
    result="UNSAT"
  elif echo "$out" | grep -q "SATISFIABLE\|VERIFICATION FAILED"; then
    result="SAT"
  elif echo "$out" | grep -q "^unsat"; then
    result="UNSAT"
  elif echo "$out" | grep -q "^sat"; then
    result="SAT"
  else
    result="UNKNOWN"
  fi

  [ -z "$solver_time" ] && solver_time="T/O"
  [ -z "$total_time" ] && total_time="T/O"
  [ -z "$vars" ] && vars=""
  [ -z "$clauses" ] && clauses=""
  [ -z "$xors" ] && xors=""

  echo "$CONFIG,$bench_name,$bench_type,$SOLVER,$run_num,$vars,$clauses,$solver_time,$total_time,$result,$xors" >> "$CSV"
  echo "  run $run_num: solver=${solver_time}s result=$result"
}

# ============================================================
# Run all benchmarks
# ============================================================
echo "=== Running benchmarks (config=$CONFIG, solver=$SOLVER, runs=$RUNS) ==="
echo ""

# C benchmarks
for bench_file in "$BENCH_DIR"/synthetic/*.c; do
  [ -f "$bench_file" ] || continue
  bench_name=$(basename "$bench_file" .c)
  echo "[$bench_name]"
  for run in $(seq 1 "$RUNS"); do
    run_one "$bench_file" "$bench_name" "c" "$run"
  done
  echo ""
done

# Real-world benchmarks
for bench_file in "$BENCH_DIR"/realworld/*.c; do
  [ -f "$bench_file" ] || continue
  bench_name=$(basename "$bench_file" .c)
  echo "[$bench_name]"
  for run in $(seq 1 "$RUNS"); do
    run_one "$bench_file" "$bench_name" "c" "$run"
  done
  echo ""
done

# SMT2 benchmarks
for bench_file in "$BENCH_DIR"/smt/*.smt2; do
  [ -f "$bench_file" ] || continue
  bench_name=$(basename "$bench_file" .smt2)
  echo "[$bench_name]"
  for run in $(seq 1 "$RUNS"); do
    run_one "$bench_file" "$bench_name" "smt2" "$run"
  done
  echo ""
done

# ============================================================
# Generate summary
# ============================================================
echo "=== Summary ==="
python3 - "$CSV" << 'PYEOF'
import sys, csv
from collections import defaultdict
import statistics

data = defaultdict(list)
with open(sys.argv[1]) as f:
    reader = csv.DictReader(f)
    for row in reader:
        key = (row['benchmark'], row['solver'])
        t = row['solver_time_s']
        if t and t != 'T/O':
            data[key].append(float(t))
        else:
            data[key].append(None)

print(f"{'Benchmark':<25} {'Solver':<10} {'Runs':>4} {'Mean':>10} {'StdDev':>10} {'Min':>10} {'Max':>10}")
print("-" * 85)
for (bench, solver), times in sorted(data.items()):
    valid = [t for t in times if t is not None]
    n = len(times)
    if valid:
        mean = statistics.mean(valid)
        sd = statistics.stdev(valid) if len(valid) > 1 else 0
        mn, mx = min(valid), max(valid)
        print(f"{bench:<25} {solver:<10} {n:>4} {mean:>10.4f} {sd:>10.4f} {mn:>10.4f} {mx:>10.4f}")
    else:
        print(f"{bench:<25} {solver:<10} {n:>4} {'T/O':>10} {'':>10} {'':>10} {'':>10}")
PYEOF

echo ""
echo "Results saved to: $OUTPUT"
echo "CSV: $CSV"
echo "System info: $OUTPUT/system_info.txt"
