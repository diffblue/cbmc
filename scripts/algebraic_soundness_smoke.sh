#!/usr/bin/env bash
# Algebraic-solver soundness smoke test.
#
# For each algebraic/soundness regression query, run smt2_solver and assert
# (a) it matches the expected verdict declared in the test's .desc, and
# (b) if z3 is on PATH, it agrees with z3 (the oracle cross-check that the
#     standard regression harness, which only matches hard-coded output, does
#     not perform). This is the lightweight CI guard against the wrong-verdict
#     bug class (adjacent-equality, deferred-replay, check-sat-assuming) that
#     the corpus differential sweep originally caught.
#
# Usage: scripts/algebraic_soundness_smoke.sh [path-to-smt2_solver]
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SMT2="${1:-$ROOT/build/bin/smt2_solver}"
TO=120
fail=0

# benchmark<TAB>expected-verdict
TESTS=$(cat <<EOF
regression/smt2_solver/adjacent-equality-soundness/test.smt2	sat
regression/smt2_solver/deferred-replay-congruence/test.smt2	unsat
regression/smt2_solver/algebraic-rabinowitsch-soundness/test.smt2	sat
regression/smt2_solver/f4-interreduce/cohencu-style-quadratic.smt2	unsat
regression/smt2_solver/basic-bv1/check-sat-assuming1.smt2	unsat
EOF
)

verdict() { grep -woE '^(sat|unsat)$' "$1" | head -1; }

if ! command -v z3 >/dev/null 2>&1; then
  echo "note: z3 not on PATH; skipping oracle cross-check"
fi

while IFS=$'\t' read -r rel exp; do
  [ -n "$rel" ] || continue
  f="$ROOT/$rel"
  if [ ! -f "$f" ]; then echo "MISSING: $rel"; fail=1; continue; fi
  ( ulimit -v 12000000; timeout "$TO" "$SMT2" --cadical "$f" ) >/tmp/smoke_ours.log 2>/dev/null
  ours=$(verdict /tmp/smoke_ours.log); ours=${ours:-TIMEOUT}
  msg="$rel: ours=$ours expected=$exp"
  if [ "$ours" != "$exp" ]; then echo "FAIL  $msg"; fail=1; continue; fi
  if command -v z3 >/dev/null 2>&1; then
    z=$( ulimit -v 12000000; timeout "$TO" z3 "$f" 2>/dev/null | grep -woE '^(sat|unsat)$' | head -1 )
    if [ "$z" = sat ] || [ "$z" = unsat ]; then
      if [ "$z" != "$ours" ]; then echo "FAIL  $msg z3=$z (DISAGREE)"; fail=1; continue; fi
      msg="$msg z3=$z"
    fi
  fi
  echo "OK    $msg"
done <<< "$TESTS"

if [ "$fail" -ne 0 ]; then echo "algebraic soundness smoke: FAILED"; exit 1; fi
echo "algebraic soundness smoke: PASSED"
