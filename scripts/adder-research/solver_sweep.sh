#!/bin/bash
# 3 solvers × 4 configs × 8 benchmarks = 96 runs, 8 parallel
set -e
CBMC=/home/ubuntu/cbmc-github.git/build/bin/cbmc
ULIMIT=6000000
TIMEOUT=300

BENCHMARKS=(
  "scripts/adder-research/benchmarks/synthetic/equiv_unsat_200.c:201:equiv"
  "scripts/adder-research/benchmarks/realworld/checksum_200.c:201:checksum"
  "scripts/adder-research/benchmarks/realworld/popcount_10.c:331:popcount"
  "scripts/adder-research/benchmarks/realworld/byte_ops_20.c:21:byte_ops"
  "scripts/adder-research/benchmarks/extended/array_sum_1000.c:1001:array_sum"
  "scripts/adder-research/benchmarks/extended/counter.c:501:counter"
  "scripts/adder-research/benchmarks/extended/hash_mix_5000.c:5001:hash_mix"
  "scripts/adder-research/benchmarks/extended/comparison_2000.c:2001:comparison"
)

# Note: --reorder-vars is CaDiCaL-specific, skip S0 for minisat2/cryptominisat
SOLVERS=("cadical" "minisat2" "cryptominisat")

TMPDIR=$(mktemp -d)

run_one() {
  local file="$1" uw="$2" flags="$3" outfile="$4"
  t=$(ulimit -v $ULIMIT; timeout $TIMEOUT $CBMC "$file" --unwind "$uw" --no-unwinding-assertions --verbosity 8 $flags 2>&1 | grep "^Runtime Solver:" | tail -1 | sed 's/Runtime Solver: //;s/s$//')
  [ -z "$t" ] && t="T/O"
  [ "$t" != "T/O" ] && t=$(printf "%.1f" "$t")
  echo "$t" > "$outfile"
}

# Header
printf "%-12s %-14s" "solver" "config"
for b in "${BENCHMARKS[@]}"; do IFS=: read -r _ _ n <<< "$b"; printf " %9s" "$n"; done
echo ""

for solver in "${SOLVERS[@]}"; do
  if [ "$solver" = "cadical" ]; then
    CONFIGS=(
      "baseline:--sat-solver cadical"
      "BK:--sat-solver cadical --adder-encoding brent-kung"
      "BK+simp:--sat-solver cadical --adder-encoding bk-simple-mult"
      "BK+simp+S0:--sat-solver cadical --adder-encoding bk-simple-mult --reorder-vars 0"
    )
  else
    CONFIGS=(
      "baseline:--sat-solver $solver"
      "BK:--sat-solver $solver --adder-encoding brent-kung"
      "BK+simp:--sat-solver $solver --adder-encoding bk-simple-mult"
    )
  fi

  for config in "${CONFIGS[@]}"; do
    IFS=: read -r clabel cflags <<< "$config"

    pids=()
    for b in "${BENCHMARKS[@]}"; do
      IFS=: read -r file uw bname <<< "$b"
      outfile="$TMPDIR/${solver}_${clabel}_${bname}"
      run_one "$file" "$uw" "$cflags" "$outfile" &
      pids+=($!)
    done
    for pid in "${pids[@]}"; do wait $pid; done

    printf "%-12s %-14s" "$solver" "$clabel"
    for b in "${BENCHMARKS[@]}"; do
      IFS=: read -r _ _ bname <<< "$b"
      printf " %9s" "$(cat $TMPDIR/${solver}_${clabel}_${bname})"
    done
    echo ""
  done
done

rm -rf "$TMPDIR"
