#!/bin/bash
# High-bitwidth scaling experiment for the algebraic procedure.
#
# Tests three classes of bit-vector polynomial identities at bitwidths
# from 64 to 4096:
#   - commutativity: bvmul a b == bvmul b a (degree 2, 1 product)
#   - associativity: bvmul (bvmul a b) c == bvmul a (bvmul b c) (degree 3, 2 products)
#   - quadratic identity: (a+b)^2 == a^2 + 2ab + b^2 (degree 2, 4 products + sums)
#   - difference of squares: (a-b)(a+b) == a^2 - b^2 (degree 2, 3 products + sums)
#
# These are universal-equational queries with polynomial expressions —
# the algebraic procedure's target fragment.
#
# Output: TSV at doc/paper-algebraic/data/high-bitwidth-scaling.tsv
set -u

CBMC_DIR=/home/ubuntu/cbmc-github.git
SMT2=$CBMC_DIR/build/bin/smt2_solver
OUT=$CBMC_DIR/doc/paper-algebraic/data/high-bitwidth-scaling.tsv
TIMEOUT=120

ulimit -v 14000000 2>/dev/null

mkdir -p "$(dirname "$OUT")"

emit_query() {
  local kind=$1; local bw=$2
  case "$kind" in
    commutativity)
      cat <<EOF
(set-logic QF_BV)
(declare-const a (_ BitVec $bw))
(declare-const b (_ BitVec $bw))
(assert (distinct (bvmul a b) (bvmul b a)))
(check-sat)
EOF
      ;;
    associativity)
      cat <<EOF
(set-logic QF_BV)
(declare-const a (_ BitVec $bw))
(declare-const b (_ BitVec $bw))
(declare-const c (_ BitVec $bw))
(assert (distinct (bvmul (bvmul a b) c) (bvmul a (bvmul b c))))
(check-sat)
EOF
      ;;
    quadratic)
      cat <<EOF
(set-logic QF_BV)
(declare-const a (_ BitVec $bw))
(declare-const b (_ BitVec $bw))
(assert (distinct
  (bvmul (bvadd a b) (bvadd a b))
  (bvadd (bvadd (bvmul a a) (bvmul (_ bv2 $bw) (bvmul a b))) (bvmul b b))))
(check-sat)
EOF
      ;;
    diffsquares)
      cat <<EOF
(set-logic QF_BV)
(declare-const a (_ BitVec $bw))
(declare-const b (_ BitVec $bw))
(assert (distinct
  (bvmul (bvsub a b) (bvadd a b))
  (bvsub (bvmul a a) (bvmul b b))))
(check-sat)
EOF
      ;;
  esac
}

run_one() {
  local kind=$1; local bw=$2; local config=$3
  local query
  query=$(emit_query "$kind" "$bw")
  local env_prefix=""
  if [ "$config" = "shift-add" ]; then
    env_prefix="DISABLE_ALGEBRAIC=1"
  fi
  local start_ts; start_ts=$(date +%s.%N)
  local result
  result=$(echo "$query" | env $env_prefix timeout "$TIMEOUT" "$SMT2" 2>&1 | grep -E "^(sat|unsat|unknown)$" | head -1)
  local end_ts; end_ts=$(date +%s.%N)
  if [ -z "$result" ]; then result="T/O"; fi
  local elapsed; elapsed=$(awk -v s="$start_ts" -v e="$end_ts" 'BEGIN{printf "%.3f", e-s}')
  echo -e "${kind}\t${bw}\t${config}\t${elapsed}\t${result}"
}

# Header
{
  echo "# High-bitwidth scaling experiment for the algebraic procedure"
  echo "# Date: $(date -Iseconds)"
  echo "# Machine: $(uname -m), $(grep 'model name' /proc/cpuinfo | head -1 | cut -d: -f2 | xargs)"
  echo "# Memory: $(free -h | grep Mem | awk '{print $2}')"
  echo "# CBMC: $($CBMC_DIR/build/bin/cbmc --version 2>/dev/null | head -1)"
  echo "# Timeout: ${TIMEOUT}s"
  echo "#"
  echo -e "kind\tbw\tconfig\ttime\tresult"
} > "$OUT"

for kind in commutativity associativity quadratic diffsquares; do
  for bw in 64 128 256 512 1024 2048 4096; do
    run_one "$kind" "$bw" default >> "$OUT"
  done
done

# shift-add baseline only at lower bw — at high bw it's hopelessly slow
for kind in commutativity associativity quadratic diffsquares; do
  for bw in 64 128 256; do
    run_one "$kind" "$bw" shift-add >> "$OUT"
  done
done

echo "Done. Results written to $OUT"
