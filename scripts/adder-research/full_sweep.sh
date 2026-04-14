#!/bin/bash
# Full sweep: 4 configs × 16 CaDiCaL options × 8 benchmarks
# Runs 8 benchmarks in parallel per config+option combination
set -e
CBMC=/home/ubuntu/cbmc-github.git/build/bin/cbmc
ULIMIT=6000000
TIMEOUT=120

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

CONFIGS=(
  "baseline:--sat-solver cadical"
  "BK:--sat-solver cadical --adder-encoding brent-kung"
  "BK+simp:--sat-solver cadical --adder-encoding bk-simple-mult"
  "BK+simp+S0:--sat-solver cadical --adder-encoding bk-simple-mult --reorder-vars 0"
)

CADICAL_OPTS=(
  "default:"
  "elimbound=16:elimbound=16"
  "elimbound=4:elimbound=4"
  "factor=1:factor=1"
  "stabilize=0:stabilize=0"
  "chrono=0:chrono=0"
  "lucky=0:lucky=0"
  "reduce=0:reduce=0"
  "elim=0:elim=0"
  "subsume=0:subsume=0"
  "vivify=0:vivify=0"
  "elim=0+sub=0:elim=0,subsume=0"
  "walk=0:walk=0"
  "target=0:target=0"
  "target=2:target=2"
  "phase=0:phase=0"
)

TMPDIR=$(mktemp -d)

run_one() {
  local file="$1" uw="$2" flags="$3" env="$4" outfile="$5"
  local cmd="ulimit -v $ULIMIT; timeout $TIMEOUT $CBMC $file --unwind $uw --no-unwinding-assertions --verbosity 8 $flags"
  [ -n "$env" ] && cmd="CADICAL_OPTS=$env $cmd"
  t=$(eval "$cmd" 2>&1 | grep "^Runtime Solver:" | tail -1 | sed 's/Runtime Solver: //;s/s$//')
  [ -z "$t" ] && t="T/O"
  [ "$t" != "T/O" ] && t=$(printf "%.1f" "$t")
  echo "$t" > "$outfile"
}

for config in "${CONFIGS[@]}"; do
  IFS=: read -r clabel cflags <<< "$config"
  for copt in "${CADICAL_OPTS[@]}"; do
    IFS=: read -r olabel oenv <<< "$copt"
    
    # Run all 8 benchmarks in parallel
    pids=()
    for b in "${BENCHMARKS[@]}"; do
      IFS=: read -r file uw bname <<< "$b"
      outfile="$TMPDIR/${clabel}_${olabel}_${bname}"
      run_one "$file" "$uw" "$cflags" "$oenv" "$outfile" &
      pids+=($!)
    done
    # Wait for all
    for pid in "${pids[@]}"; do wait $pid; done
    
    # Collect results
    printf "%-12s %-14s" "$clabel" "$olabel"
    for b in "${BENCHMARKS[@]}"; do
      IFS=: read -r _ _ bname <<< "$b"
      outfile="$TMPDIR/${clabel}_${olabel}_${bname}"
      printf " %8s" "$(cat $outfile)"
    done
    echo ""
  done
done

rm -rf "$TMPDIR"
