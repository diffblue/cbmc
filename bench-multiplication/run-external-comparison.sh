#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
SMT2="$ROOT/build/bin/smt2_solver"
BITWUZLA="$HOME/bitwuzla.git/build/src/main/bitwuzla"
CVC5="$(which cvc5)"
BENCH="$SCRIPT_DIR/smt-comp"
TIMEOUT=${1:-120}
RUNS=${2:-3}
JOBS=${3:-8}

WORKDIR=$(mktemp -d /tmp/bench-ext.XXXXXX)
trap 'rm -rf "$WORKDIR"' EXIT

median() {
  local times=()
  for ((i = 0; i < RUNS; i++)); do
    local start end elapsed result
    start=$(date +%s%N)
    result=$(ulimit -v 6000000; eval timeout -s 9 "$TIMEOUT" "$@" 2>&1) || true
    end=$(date +%s%N)
    elapsed=$(echo "scale=6; ($end - $start) / 1000000000" | bc)
    if echo "$result" | grep -qE "^(sat|unsat)$"; then
      times+=("$elapsed")
    else
      times+=("999999")
    fi
  done
  printf '%s\n' "${times[@]}" | sort -g | sed -n "$(( (RUNS+1)/2 ))p" | sed 's/^999999$/T\/O/'
}

JOBID=0
enqueue() {
  local solver="$1" label="$2" cmd="$3"
  local jid=$((JOBID++))
  (
    local t
    t=$(median "$cmd")
    printf '%s\t%s\t%s\n' "$solver" "$label" "$t" > "$WORKDIR/$jid.tsv"
    printf '  [%d] %s/%s = %s\n' "$jid" "$solver" "$label" "$t" >&2
  ) &
  if (( (JOBID % JOBS) == 0 )); then wait; fi
}

cat << EOF
# External solver comparison on QF_BV benchmarks
# Date: $(date -Iseconds)
# Timeout: ${TIMEOUT}s, Runs: $RUNS (median), Jobs: $JOBS
# CBMC smt2_solver: $($SMT2 --cadical < /dev/null 2>&1 | grep "Solving with" | sed 's/.*Solving with //' || echo "?")
# Bitwuzla: $($BITWUZLA --version 2>&1 | head -1 || echo "?")
# cvc5: $($CVC5 --version 2>&1 | head -1 || echo "?")
#
solver	benchmark	time
EOF

echo "Starting comparison..." >&2

for f in "$BENCH"/*.smt2; do
  label=$(basename "$f" .smt2)
  # CBMC with CaDiCaL (default config):
  enqueue "cbmc-cadical" "$label" "'$SMT2' --cadical '$f'"
  # CBMC with MiniSat:
  enqueue "cbmc-minisat" "$label" "'$SMT2' '$f'"
  # Bitwuzla:
  enqueue "bitwuzla" "$label" "'$BITWUZLA' '$f'"
  # cvc5:
  enqueue "cvc5" "$label" "'$CVC5' --lang smt2 '$f'"
done

wait
echo "All $JOBID jobs complete." >&2
cat "$WORKDIR"/*.tsv 2>/dev/null | sort -t$'\t' -k2,2 -k1,1
