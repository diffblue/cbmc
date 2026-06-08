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
SMT2_MS="$ROOT_DIR/build-mergesat/bin/smt2_solver"
BENCH="$SCRIPT_DIR"

[[ -x "$CBMC" ]] || { echo "Missing: $CBMC" >&2; exit 1; }
[[ -x "$SMT2" ]] || { echo "Missing: $SMT2" >&2; exit 1; }
HAVE_MS=false; [[ -x "$CBMC_MS" ]] && HAVE_MS=true
HAVE_SMT2_MS=false; [[ -x "$SMT2_MS" ]] && HAVE_SMT2_MS=true

WORKDIR=$(mktemp -d /tmp/bench-mul.XXXXXX)
trap 'rm -rf "$WORKDIR"' EXIT

# --- Single run: return solver time or wall time or T/O ---
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
# Output columns: suite solver mul_enc adder_enc benchmark time
JOBID=0
enqueue() {
  local suite="$1" solver="$2" mul_enc="$3" adder_enc="$4" label="$5"
  shift 5
  local cmd="$*"
  local jid=$((JOBID++))
  (
    local t
    t=$(median "$cmd")
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$suite" "$solver" "$mul_enc" "$adder_enc" "$label" "$t" \
      > "$WORKDIR/$jid.tsv"
    printf '  [%d] %s/%s+%s/%s = %s\n' \
      "$jid" "$solver" "$mul_enc" "$adder_enc" "$label" "$t" >&2
  ) &
  if (( (JOBID % JOBS) == 0 )); then wait; fi
}

# --- cbmc helper ---
cbmc_job() {
  local solver="$1" mul_enc="$2" adder_enc="$3" label="$4" src="$5"
  shift 5
  local extra="$*"
  local bin="$CBMC" sflag="" aflag=""
  case "$solver" in
    cadical)       sflag="--sat-solver cadical" ;;
    cryptominisat) sflag="--sat-solver cryptominisat" ;;
    mergesat)      bin="$CBMC_MS" ;;
  esac
  [[ "$adder_enc" != "ripple" ]] && aflag="--adder-encoding $adder_enc"
  enqueue cbmc "$solver" "$mul_enc" "$adder_enc" "$label" \
    "'$bin' '$src' $extra --no-standard-checks --verbosity 10 --multiplier-encoding $mul_enc $aflag $sflag"
}

# --- smt2 helper ---
smt2_job() {
  local solver="$1" mul_enc="$2" adder_enc="$3" label="$4" src="$5"
  local bin="$SMT2" sflag="" aflag=""
  case "$solver" in
    cadical)       sflag="--cadical" ;;
    cryptominisat) sflag="--cryptominisat" ;;
    mergesat)      bin="$SMT2_MS" ;;
  esac
  [[ "$adder_enc" != "ripple" ]] && aflag="--adder-encoding $adder_enc"
  enqueue smt2 "$solver" "$mul_enc" "$adder_enc" "$label" \
    "'$bin' $sflag --multiplier-encoding $mul_enc $aflag '$src'"
}

# =====================================================================
# SUITES
# =====================================================================

MUL_ENCS=(shift-add dadda comba comba-cs)
ADDER_ENCS=(ripple brent-kung g-only)

run_cbmc() {
  echo "# cbmc suite" >&2
  local solvers=(minisat cadical cryptominisat)
  $HAVE_MS && solvers+=(mergesat)

  # Commutativity scaling: all mul × adder × solver
  for bw in 9 11 13; do
    for me in "${MUL_ENCS[@]}"; do
      for ae in "${ADDER_ENCS[@]}"; do
        for s in "${solvers[@]}"; do
          cbmc_job "$s" "$me" "$ae" "comm_$bw" "$BENCH/comm.c" "-DBW=$bw"
        done
      done
    done
  done

  # Matrix trace: all mul × adder × solver
  for me in "${MUL_ENCS[@]}"; do
    for ae in "${ADDER_ENCS[@]}"; do
      for s in "${solvers[@]}"; do
        cbmc_job "$s" "$me" "$ae" "matrix_trace" "$BENCH/matrix_mul.c"
      done
    done
  done

  # MAC commutativity (CaDiCaL only, all mul × adder)
  for me in "${MUL_ENCS[@]}"; do
    for ae in "${ADDER_ENCS[@]}"; do
      cbmc_job cadical "$me" "$ae" "mac_comm" "$BENCH/mac_equiv.c"
    done
  done

  # Overflow (CaDiCaL, key encodings)
  for me in shift-add dadda comba-cs; do
    cbmc_job cadical "$me" ripple "overflow_16" "$BENCH/overflow_check.c" "-DBW=16"
  done

  # Industrial (CaDiCaL, shift-add vs comba-cs, ripple only)
  for ind in murmurhash3_fmix keyed_hash fir_tap div_by_const; do
    local src="$BENCH/industrial/${ind}.c"
    [[ -f "$src" ]] || continue
    for me in shift-add comba-cs; do
      cbmc_job cadical "$me" ripple "$ind" "$src"
    done
  done
}

run_smt2() {
  echo "# smt2 suite" >&2
  local smt_dir="$BENCH/smt-comp"
  [[ -d "$smt_dir" ]] || { echo "No smt-comp dir" >&2; return; }
  local solvers=(cadical cryptominisat minisat)
  $HAVE_SMT2_MS && solvers+=(mergesat)

  for f in "$smt_dir"/*.smt2; do
    local label
    label=$(basename "$f" .smt2)
    for me in "${MUL_ENCS[@]}"; do
      for ae in "${ADDER_ENCS[@]}"; do
        for s in "${solvers[@]}"; do
          smt2_job "$s" "$me" "$ae" "$label" "$f"
        done
      done
    done
  done
}

run_quick() {
  echo "# quick suite" >&2
  for me in shift-add comba-cs; do
    for ae in ripple brent-kung; do
      cbmc_job cadical "$me" "$ae" "comm_9" "$BENCH/comm.c" "-DBW=9"
      smt2_job cadical "$me" "$ae" "comm_8_smt2" "$BENCH/smt-comp/comm_8.smt2"
    done
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
# Mul encodings: ${MUL_ENCS[*]}
# Adder encodings: ${ADDER_ENCS[*]}
EOF
$HAVE_MS && echo "# MergeSat: available (cbmc)"
$HAVE_SMT2_MS && echo "# MergeSat: available (smt2_solver)"
printf '#\nsuite\tsolver\tmul_enc\tadder_enc\tbenchmark\ttime\n'

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

cat "$WORKDIR"/*.tsv 2>/dev/null | sort -t$'\t' -k1,1 -k5,5 -k2,2 -k3,3 -k4,4
