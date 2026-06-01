#!/bin/bash
# Ablation audit: for each benchmark run algebra-ON vs DISABLE_ALGEBRAIC=1.
# Usage: ablation.sh <list-of-abs-paths> <timeout> <jobs> <out-tsv>
# Output columns: path  v_on  t_on  v_off  t_off  class
#   class: NEEDS_ALGEBRA (on solves, off TO)
#          ALGEBRA_FASTER (both solve, on >=3x faster AND saves >=5s)
#          ARTIFACT       (both solve, comparable)
#          BOTH_TO        (neither solves)
#          ONLY_OFF       (off solves, on doesn't -- algebra harmful)
set -u
LIST="$1"; TO="$2"; JOBS="$3"; OUT="$4"
SOLVER=/home/ubuntu/cbmc-github.git/build/bin/smt2_solver

one() {
  local f="$1" to="$2" von toff voff ton s e
  s=$(date +%s.%N)
  von=$( ulimit -v 8000000 2>/dev/null; timeout "$to" "$SOLVER" < "$f" 2>/dev/null | grep -aE '^(sat|unsat|unknown)$' | head -1 )
  e=$(date +%s.%N); ton=$(echo "$e-$s"|bc)
  s=$(date +%s.%N)
  voff=$( ulimit -v 8000000 2>/dev/null; DISABLE_ALGEBRAIC=1 timeout "$to" "$SOLVER" < "$f" 2>/dev/null | grep -aE '^(sat|unsat|unknown)$' | head -1 )
  e=$(date +%s.%N); toff=$(echo "$e-$s"|bc)
  [ -z "$von" ] && von=TO; [ -z "$voff" ] && voff=TO
  local cls
  sol() { [ "$1" = sat ] || [ "$1" = unsat ]; }
  if sol "$von" && ! sol "$voff"; then cls=NEEDS_ALGEBRA
  elif ! sol "$von" && sol "$voff"; then cls=ONLY_OFF
  elif ! sol "$von" && ! sol "$voff"; then cls=BOTH_TO
  else
    # both solve
    if awk "BEGIN{exit !($toff>=3*$ton && $toff-$ton>=5)}"; then cls=ALGEBRA_FASTER
    else cls=ARTIFACT; fi
  fi
  printf '%s\t%s\t%.2f\t%s\t%.2f\t%s\n' "$f" "$von" "$ton" "$voff" "$toff" "$cls"
}
export -f one; export SOLVER
: > "$OUT"
cat "$LIST" | xargs -P "$JOBS" -I {} bash -c 'one "$@"' _ {} "$TO" >> "$OUT"
echo "Done: $(wc -l <"$OUT") in $OUT"
