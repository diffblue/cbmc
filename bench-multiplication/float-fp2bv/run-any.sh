#!/bin/bash
# Usage: run-any.sh <list> <timeout> <jobs> <out-tsv> <tag> <mode> <solver...>
# mode: stdin | filearg
set -u
LIST="$1"; TO="$2"; JOBS="$3"; OUT="$4"; TAG="$5"; MODE="$6"; shift 6
SOLVER="$*"
ROOT=/home/ubuntu/bench-staging/non-incremental/QF_BV

run_one() {
  local f="$1" to="$2" mode="$3"; shift 3; local solver="$*"
  local fam rel size start end verdict
  rel="${f#./}"; fam="${rel%%/*}"
  size=$(stat -c%s "$f" 2>/dev/null || echo 0)
  start=$(date +%s.%N)
  if [ "$mode" = stdin ]; then
    verdict=$( ( ulimit -v 8000000 2>/dev/null; timeout "$to" $solver < "$f" 2>/dev/null ) \
               | grep -aE '^(sat|unsat|unknown)$' | head -1)
  else
    verdict=$( ( ulimit -v 8000000 2>/dev/null; timeout "$to" $solver "$f" 2>/dev/null ) \
               | grep -aE '^(sat|unsat|unknown)$' | head -1)
  fi
  end=$(date +%s.%N)
  [ -z "$verdict" ] && verdict="TO/ERR"
  printf '%s\t%s\t%s\t%.2f\t%s\n' "$fam" "$rel" "$verdict" \
    "$(echo "$end - $start" | bc)" "$size"
}
export -f run_one
cd "$ROOT"
: > "$OUT"
cat "$LIST" | xargs -P "$JOBS" -I {} bash -c 'run_one "$@"' _ {} "$TO" "$MODE" "$SOLVER" >> "$OUT"
echo "[$TAG] Done: $(wc -l < "$OUT") results"
