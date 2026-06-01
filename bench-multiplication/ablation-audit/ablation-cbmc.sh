#!/bin/bash
# cbmc ablation: ON vs DISABLE_ALGEBRAIC=1.  result via VERIFICATION (SUCCESSFUL/FAILED)
# Usage: ablation-cbmc.sh <timeout> <out-tsv> -- "<label> <cbmc-args...>" ...
set -u
CBMC=/home/ubuntu/cbmc-github.git/build/bin/cbmc
TO="$1"; OUT="$2"; shift 2; shift   # drop the --
: > "$OUT"
runv() { # $1=label-args
  local args="$1" label v
  label="${args%% *}"; local rest="${args#* }"
  local s e ton toff von voff
  s=$(date +%s.%N)
  von=$( ulimit -v 12000000 2>/dev/null; timeout "$TO" $CBMC $rest --no-standard-checks 2>/dev/null \
         | grep -aoE "VERIFICATION (SUCCESSFUL|FAILED)" | head -1)
  e=$(date +%s.%N); ton=$(echo "$e-$s"|bc)
  s=$(date +%s.%N)
  voff=$( ulimit -v 12000000 2>/dev/null; DISABLE_ALGEBRAIC=1 timeout "$TO" $CBMC $rest --no-standard-checks 2>/dev/null \
         | grep -aoE "VERIFICATION (SUCCESSFUL|FAILED)" | head -1)
  e=$(date +%s.%N); toff=$(echo "$e-$s"|bc)
  [ -z "$von" ] && von=TO; [ -z "$voff" ] && voff=TO
  local sol_on=0 sol_off=0
  [ "$von" = "VERIFICATION SUCCESSFUL" ] && sol_on=1
  [ "$voff" = "VERIFICATION SUCCESSFUL" ] && sol_off=1
  local cls
  if [ $sol_on = 1 ] && [ $sol_off = 0 ]; then cls=NEEDS_ALGEBRA
  elif [ $sol_on = 0 ] && [ $sol_off = 1 ]; then cls=ONLY_OFF
  elif [ $sol_on = 0 ] && [ $sol_off = 0 ]; then cls=BOTH_TO
  elif awk "BEGIN{exit !($toff>=3*$ton && $toff-$ton>=5)}"; then cls=ALGEBRA_FASTER
  else cls=ARTIFACT; fi
  printf '%s\t%s\t%.2f\t%s\t%.2f\t%s\n' "$label" "$von" "$ton" "$voff" "$toff" "$cls" | tee -a "$OUT"
}
for spec in "$@"; do runv "$spec"; done
