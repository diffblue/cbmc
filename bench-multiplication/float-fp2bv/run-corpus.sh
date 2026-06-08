#!/bin/bash
# Parallel evaluation harness for the widened QF_BV corpus.
# Usage: run-corpus.sh <list-file> <timeout-s> <jobs> <out-tsv> [solver]
# Records: family, relpath, verdict, wall_s, size_bytes
set -u
LIST="$1"; TO="$2"; JOBS="$3"; OUT="$4"
SOLVER="${5:-/home/ubuntu/cbmc-github.git/build/bin/smt2_solver}"
ROOT=/home/ubuntu/bench-staging/non-incremental/QF_BV

run_one() {
  local f="$1" to="$2" solver="$3"
  local fam rel size start end verdict
  rel="${f#./}"
  fam="${rel%%/*}"
  size=$(stat -c%s "$f" 2>/dev/null || echo 0)
  start=$(date +%s.%N)
  verdict=$(ulimit -v 8000000 2>/dev/null; timeout "$to" "$solver" < "$f" 2>/dev/null \
            | grep -aE '^(sat|unsat|unknown)$' | head -1)
  end=$(date +%s.%N)
  [ -z "$verdict" ] && verdict="TO/ERR"
  printf '%s\t%s\t%s\t%.2f\t%s\n' "$fam" "$rel" "$verdict" \
    "$(echo "$end - $start" | bc)" "$size"
}
export -f run_one
export SOLVER

cd "$ROOT"
: > "$OUT"
cat "$LIST" | xargs -P "$JOBS" -I {} bash -c 'run_one "$@"' _ {} "$TO" "$SOLVER" >> "$OUT"
echo "Done: $(wc -l < "$OUT") results in $OUT"
