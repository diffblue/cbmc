#!/usr/bin/env bash
# bench-multiplication/run-benchmarks.sh
#
# Reproducible benchmark runner for the multiplication encoding paper.
#
# Usage:
#   ./run-benchmarks.sh                  # full suite
#   ./run-benchmarks.sh --suite cbmc     # cbmc benchmarks only
#   ./run-benchmarks.sh --suite smt2     # smt2 benchmarks only
#   ./run-benchmarks.sh --suite quick    # fast subset for smoke testing
#   ./run-benchmarks.sh --runs 5         # 5 runs per config (default: 3)
#   ./run-benchmarks.sh --jobs 4         # 4 parallel jobs (default: 8)
#   ./run-benchmarks.sh --timeout 60     # 60s timeout (default: 120)
#
# Output: TSV to stdout, progress to stderr.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

RUNS=3
JOBS=8
TIMEOUT=120
MEMLIMIT=6000000
SUITE="all"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --runs)    RUNS="$2"; shift 2 ;;
    --jobs)    JOBS="$2"; shift 2 ;;
    --timeout) TIMEOUT="$2"; shift 2 ;;
    --suite)   SUITE="$2"; shift 2 ;;
    --help|-h) sed -n '2,/^$/p' "$0" | sed 's/^# \?//'; exit 0 ;;
    *) echo "Unknown: $1" >&2; exit 1 ;;
  esac
done

CBMC="$ROOT_DIR/build/bin/cbmc"
CBMC_MS="$ROOT_DIR/build-mergesat/bin/cbmc"
SMT2="$ROOT_DIR/build/bin/smt2_solver"
BENCH="$SCRIPT_DIR"

[[ -x "$CBMC" ]] || { echo "Missing: $CBMC" >&2; exit 1; }
[[ -x "$SMT2" ]] || { echo "Missing: $SMT2" >&2; exit 1; }
HAVE_MS=false; [[ -x "$CBMC_MS" ]] && HAVE_MS=true

WORKDIR=$(mktemp -d /tmp/bench-mul.XXXXXX)
trap 'rm -rf "$WORKDIR"' EXIT

# --- Run one command, return solver time or wall time or T/O ---
run_once() {
  local start end elapsed solver_time result
  start=$(date +%s%N)
  result=$(ulimit -v "$MEMLIMIT"; eval timeout -s 9 "$TIMEOUT" "$@" 2>&1) || true
  end=$(date +%s%N)
  elapsed=$(echo "scale=6; ($end - $start) / 1000000000" | bc)
  solver_time=$(echo "$result" | grep "^Runtime Solver:" | tail -1 |
    sed 's/Runtime Solver: //;s/s$//')
  if [[ -n "$solver_time" ]]; then
    echo "$solver_time"
  elif echo "$result" | grep -qE "^(VERIFICATION|sat$|unsat$)"; then
    echo "$elapsed"
  else
    echo "T/O"
  fi
}

# --- Median of N runs ---
median() {
  local times=()
  for ((i = 0; i < RUNS; i++)); do
    times+=("$(run_once "$@")")
  done
  printf '%s\n' "${times[@]}" |
    sed 's/^T\/O$/999999/' | sort -g |
    sed -n "$(( (RUNS + 1) / 2 ))p" |
    sed 's/^999999$/T\/O/'
}

# --- Enqueue a job ---
JOBID=0
enqueue() {
  local suite="$1" solver="$2" enc="$3" label="$4"
  shift 4
  local cmd="$*"
  local jid=$((JOBID++))
  (
    local t
    t=$(median "$cmd")
    printf '%s\t%s\t%s\t%s\t%s\n' "$suite" "$solver" "$enc" "$label" "$t" \
      > "$WORKDIR/$jid.tsv"
    printf '  [%d] %s/%s/%s = %s\n' "$jid" "$solver" "$enc" "$label" "$t" >&2
  ) &
  if (( (JOBID % JOBS) == 0 )); then wait; fi
}

# --- cbmc helper: enqueue one cbmc run ---
cbmc_job() {
  local solver="$1" enc="$2" label="$3" src="$4"
  shift 4
  local extra="$*"
  local bin="$CBMC"
  local sflag=""
  case "$solver" in
    cadical)       sflag="--sat-solver cadical" ;;
    cryptominisat) sflag="--sat-solver cryptominisat" ;;
    mergesat)      bin="$CBMC_MS"; sflag="" ;;
    minisat)       sflag="" ;;
  esac
  enqueue cbmc "$solver" "$enc" "$label" \
    "'$bin' '$src' $extra --no-standard-checks --verbosity 10 --multiplier-encoding $enc $sflag"
}

# --- smt2 helper ---
smt2_job() {
  local solver="$1" enc="$2" label="$3" src="$4"
  local sflag=""
  [[ "$solver" == "cadical" ]] && sflag="--cadical"
  enqueue smt2 "$solver" "$enc" "$label" \
    "'$SMT2' $sflag --multiplier-encoding $enc '$src'"
}

# =====================================================================
# SUITES
# =====================================================================

run_cbmc() {
  echo "# cbmc suite" >&2
  local solvers=(minisat cadical cryptominisat)
  $HAVE_MS && solvers+=(mergesat)
  local encs=(shift-add dadda comba comba-cs)

  # Commutativity scaling
  for bw in 9 11 13; do
    for enc in "${encs[@]}"; do
      for s in "${solvers[@]}"; do
        cbmc_job "$s" "$enc" "comm_$bw" "$BENCH/comm.c" "-DBW=$bw"
      done
    done
  done

  # Matrix trace
  for enc in "${encs[@]}"; do
    for s in "${solvers[@]}"; do
      cbmc_job "$s" "$enc" "matrix_trace" "$BENCH/matrix_mul.c"
    done
  done

  # MAC commutativity
  for enc in "${encs[@]}"; do
    cbmc_job cadical "$enc" "mac_comm" "$BENCH/mac_equiv.c"
  done

  # Overflow
  for enc in shift-add dadda comba-cs; do
    cbmc_job cadical "$enc" "overflow_16" "$BENCH/overflow_check.c" "-DBW=16"
  done

  # Industrial
  for ind in murmurhash3_fmix keyed_hash fir_tap div_by_const; do
    local src="$BENCH/industrial/${ind}.c"
    [[ -f "$src" ]] || continue
    for enc in shift-add comba-cs; do
      cbmc_job cadical "$enc" "$ind" "$src"
    done
  done

  # Strength reduction
  if [[ -f "$BENCH/strength_reduce.c" ]]; then
    for enc in shift-add comba-cs; do
      cbmc_job cadical "$enc" "strength_red" "$BENCH/strength_reduce.c"
    done
  fi
}

run_smt2() {
  echo "# smt2 suite" >&2
  local smt_dir="$BENCH/smt-comp"
  [[ -d "$smt_dir" ]] || { echo "No smt-comp dir" >&2; return; }
  local smt2_ms="$ROOT_DIR/build-mergesat/bin/smt2_solver"
  for f in "$smt_dir"/*.smt2; do
    local label
    label=$(basename "$f" .smt2)
    for enc in shift-add dadda comba comba-cs; do
      smt2_job cadical "$enc" "$label" "$f"
      # CryptoMiniSat
      enqueue smt2 cryptominisat "$enc" "$label" \
        "'$SMT2' --cryptominisat --multiplier-encoding $enc '$f'"
    done
    # MiniSat
    for enc in shift-add comba-cs; do
      smt2_job minisat "$enc" "$label" "$f"
    done
    # MergeSat (separate binary, default solver)
    if [[ -x "$smt2_ms" ]]; then
      for enc in shift-add comba-cs; do
        enqueue smt2 mergesat "$enc" "$label" \
          "'$smt2_ms' --multiplier-encoding $enc '$f'"
      done
    fi
  done
}

run_quick() {
  echo "# quick suite" >&2
  for enc in shift-add comba-cs; do
    cbmc_job cadical "$enc" "comm_9" "$BENCH/comm.c" "-DBW=9"
    smt2_job cadical "$enc" "comm_8_smt2" "$BENCH/smt-comp/comm_8.smt2"
  done
}

# =====================================================================
# MAIN
# =====================================================================

cat << EOF
# Multiplication encoding benchmark results
# Date: $(date -Iseconds)
# Machine: $(lscpu | grep 'Model name' | sed 's/.*: *//')
# Memory: $(free -h | awk '/Mem:/{print $2}')
# OS: $(grep PRETTY_NAME /etc/os-release | cut -d'"' -f2)
# GCC: $(gcc --version | head -1)
# CBMC: $("$CBMC" --version 2>&1 | head -1)
# Runs: $RUNS (median), Timeout: ${TIMEOUT}s, Memlimit: $((MEMLIMIT/1024/1024))GB, Jobs: $JOBS
# Solvers: CaDiCaL $(cat "$ROOT_DIR/build/cadical-src/VERSION" 2>/dev/null || echo '?'), MiniSat 2.2.1, CryptoMiniSat 5.11.21
EOF
$HAVE_MS && echo "# MergeSat: available"
printf '#\nsuite\tsolver\tencoding\tbenchmark\ttime\n'

echo "Starting ($SUITE, jobs=$JOBS, runs=$RUNS, timeout=${TIMEOUT}s)..." >&2

case "$SUITE" in
  all)   run_cbmc; wait; run_smt2 ;;
  cbmc)  run_cbmc ;;
  smt2)  run_smt2 ;;
  quick) run_quick ;;
  *) echo "Unknown suite: $SUITE" >&2; exit 1 ;;
esac

wait
echo "All $JOBID jobs complete." >&2

# Collect and sort
cat "$WORKDIR"/*.tsv 2>/dev/null | sort -t$'\t' -k1,1 -k4,4 -k2,2 -k3,3
