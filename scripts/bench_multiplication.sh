#!/bin/bash
# Comprehensive multiplication encoding benchmark suite for CBMC
#
# Builds multiple CBMC variants (encoding × SAT solver), then runs ALL
# benchmarks across ALL variants, solver backends, and refinement modes.
#
# Usage:
#   ./scripts/bench_multiplication.sh                # full run (~hours)
#   ./scripts/bench_multiplication.sh --quick         # reduced (~15 min)
#   ./scripts/bench_multiplication.sh --download-only  # just fetch benchmarks
#   ./scripts/bench_multiplication.sh --skip-build     # reuse existing builds

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
BENCH_DIR="$ROOT_DIR/bench-multiplication"
RESULTS_DIR="$ROOT_DIR/bench-results"
BUILD_BASE="$ROOT_DIR/build-bench"
BV_UTILS="$ROOT_DIR/src/solvers/flattening/bv_utils.cpp"
REFINE_SRC="$ROOT_DIR/src/solvers/refinement/refine_arithmetic.cpp"
TIMEOUT=120
RUNS=3

QUICK=false; DOWNLOAD_ONLY=false; SKIP_BUILD=false
for arg in "$@"; do
  case $arg in
    --quick) QUICK=true; TIMEOUT=30; RUNS=1 ;;
    --download-only) DOWNLOAD_ONLY=true ;;
    --skip-build) SKIP_BUILD=true ;;
  esac
done

# ============================================================
# Encoding variants (compile-time flags)
# ============================================================
# Format: "name:flags" where flags are space-separated
ENCODINGS=(
  "baseline:-DNO_COMBA"
  "comba:"
  "dadda:-DNO_COMBA -DDADDA_TREE"
  "wallace:-DNO_COMBA -DWALLACE_TREE"
  "radix4:-DNO_COMBA -DRADIX_MULTIPLIER=4"
  "radix8:-DNO_COMBA -DRADIX_MULTIPLIER=8"
  "radix8-dadda:-DNO_COMBA -DRADIX_MULTIPLIER=8 -DDADDA_TREE"
  "radix8-comba:-DRADIX_MULTIPLIER=8"
  "karatsuba:-DNO_COMBA -DUSE_KARATSUBA"
  "toom-cook:-DNO_COMBA -DUSE_TOOM_COOK"
)
if $QUICK; then
  ENCODINGS=("baseline:-DNO_COMBA" "comba:" "dadda:-DNO_COMBA -DDADDA_TREE")
fi

SAT_SOLVERS=("cadical" "minisat2")
$QUICK && SAT_SOLVERS=("cadical")

# ============================================================
# Benchmark creation
# ============================================================
create_benchmarks() {
  mkdir -p "$BENCH_DIR" "$BENCH_DIR/smt-comp"

  # Synthetic benchmarks (same as before, abbreviated for space)
  for name in comm distrib assoc const3 factor square mul_overflow mul_shift \
              mul_negation mul_double mul_bounds mul_zero_factor mul_square_nonneg; do
    [ -f "$BENCH_DIR/${name}.c" ] && continue
    echo "  Creating $name.c"
  done

  # Create all synthetic benchmarks
  cat > "$BENCH_DIR/comm.c" << 'EOF'
#ifndef BW
#define BW 9
#endif
int main() { __CPROVER_bitvector[BW] a,b,c=a*b,d=b*a; __CPROVER_assert(c==d,"comm"); }
EOF
  cat > "$BENCH_DIR/distrib.c" << 'EOF'
#ifndef BW
#define BW 9
#endif
int main() { __CPROVER_bitvector[BW] a,b,c,l=a*(b+c),r=a*b+a*c; __CPROVER_assert(l==r,"distrib"); }
EOF
  cat > "$BENCH_DIR/assoc.c" << 'EOF'
#ifndef BW
#define BW 9
#endif
int main() { __CPROVER_bitvector[BW] a,b,c,ab=a*b,bc=b*c; __CPROVER_assert(ab*c==a*bc,"assoc"); }
EOF
  cat > "$BENCH_DIR/const3.c" << 'EOF'
#ifndef BW
#define BW 9
#endif
int main() { __CPROVER_bitvector[BW] a; __CPROVER_assert(a*3==a+a+a,"const3"); }
EOF
  cat > "$BENCH_DIR/factor.c" << 'EOF'
#ifndef BW
#define BW 9
#endif
int main() { __CPROVER_bitvector[BW] p,q; __CPROVER_assume(p>1&&q>1); __CPROVER_assert(p*q!=143,"factor"); }
EOF
  cat > "$BENCH_DIR/square.c" << 'EOF'
#ifndef BW
#define BW 9
#endif
int main() { __CPROVER_bitvector[BW] a,b,s=a+b,l=s*s,r=a*a+(__CPROVER_bitvector[BW])2*a*b+b*b; __CPROVER_assert(l==r,"square"); }
EOF
  cat > "$BENCH_DIR/mul_overflow.c" << 'EOF'
#ifndef BW
#define BW 16
#endif
int main() { __CPROVER_bitvector[BW] a,b,n=a*b; __CPROVER_bitvector[BW*2] w=(__CPROVER_bitvector[BW*2])a*(__CPROVER_bitvector[BW*2])b; __CPROVER_assert(n==(__CPROVER_bitvector[BW])w,"overflow"); }
EOF
  cat > "$BENCH_DIR/mul_shift.c" << 'EOF'
#ifndef BW
#define BW 16
#endif
int main() { __CPROVER_bitvector[BW] a; __CPROVER_assert(a*4==a<<2,"shift"); }
EOF
  cat > "$BENCH_DIR/mul_negation.c" << 'EOF'
#ifndef BW
#define BW 16
#endif
int main() { __CPROVER_bitvector[BW] a; __CPROVER_assert(a*(__CPROVER_bitvector[BW])(-1)==-a,"neg"); }
EOF
  cat > "$BENCH_DIR/mul_double.c" << 'EOF'
#ifndef BW
#define BW 16
#endif
int main() { __CPROVER_bitvector[BW] a,b; __CPROVER_bitvector[BW/2] al=a,bl=b,pl=a*b; __CPROVER_assert(pl==(__CPROVER_bitvector[BW/2])(al*bl),"double"); }
EOF
  cat > "$BENCH_DIR/mul_bounds.c" << 'EOF'
#ifndef BW
#define BW 16
#endif
int main() { __CPROVER_bitvector[BW/2] a,b; __CPROVER_bitvector[BW] w=(__CPROVER_bitvector[BW])a*(__CPROVER_bitvector[BW])b; __CPROVER_bitvector[BW*2] w2=(__CPROVER_bitvector[BW*2])a*(__CPROVER_bitvector[BW*2])b; __CPROVER_assert(w==(__CPROVER_bitvector[BW])w2,"bounds"); }
EOF
  cat > "$BENCH_DIR/mul_zero_factor.c" << 'EOF'
#ifndef BW
#define BW 8
#endif
int main() { __CPROVER_bitvector[BW] a,b,r=a*b; __CPROVER_assume(r==0); __CPROVER_assume(a!=0); __CPROVER_assume(b!=0); __CPROVER_assert(0,"zero_div"); }
EOF
  cat > "$BENCH_DIR/mul_square_nonneg.c" << 'EOF'
#ifndef BW
#define BW 9
#endif
int main() { __CPROVER_bitvector[BW] a; __CPROVER_bitvector[BW*2] w=(__CPROVER_bitvector[BW*2])a*(__CPROVER_bitvector[BW*2])a; __CPROVER_assert(w>=a,"sq_nn"); }
EOF

  # SMT-COMP benchmarks
  for bw in 8 16 32; do
    cat > "$BENCH_DIR/smt-comp/comm_${bw}.smt2" << SEOF
(set-logic QF_BV)(declare-fun a () (_ BitVec $bw))(declare-fun b () (_ BitVec $bw))(assert (not (= (bvmul a b) (bvmul b a))))(check-sat)(exit)
SEOF
  done
  for bw in 8 16; do
    cat > "$BENCH_DIR/smt-comp/distrib_${bw}.smt2" << SEOF
(set-logic QF_BV)(declare-fun a () (_ BitVec $bw))(declare-fun b () (_ BitVec $bw))(declare-fun c () (_ BitVec $bw))(assert (not (= (bvmul a (bvadd b c)) (bvadd (bvmul a b) (bvmul a c)))))(check-sat)(exit)
SEOF
  done
  cat > "$BENCH_DIR/smt-comp/assoc_8.smt2" << 'EOF'
(set-logic QF_BV)(declare-fun a () (_ BitVec 8))(declare-fun b () (_ BitVec 8))(declare-fun c () (_ BitVec 8))(assert (not (= (bvmul (bvmul a b) c) (bvmul a (bvmul b c)))))(check-sat)(exit)
EOF
  for spec in "12:143" "16:10403" "20:101101"; do
    bw=${spec%%:*}; comp=${spec##*:}
    cat > "$BENCH_DIR/smt-comp/factor_${bw}.smt2" << SEOF
(set-logic QF_BV)(declare-fun p () (_ BitVec $bw))(declare-fun q () (_ BitVec $bw))(assert (bvugt p (_ bv1 $bw)))(assert (bvugt q (_ bv1 $bw)))(assert (= (bvmul p q) (_ bv${comp} $bw)))(check-sat)(exit)
SEOF
  done
  cat > "$BENCH_DIR/smt-comp/mixed_arith_8.smt2" << 'EOF'
(set-logic QF_BV)(declare-fun a () (_ BitVec 8))(declare-fun b () (_ BitVec 8))(declare-fun c () (_ BitVec 8))(declare-fun d () (_ BitVec 8))(assert (not (= (bvadd (bvmul a b) (bvmul c d)) (bvsub (bvsub (bvmul (bvadd a c) (bvadd b d)) (bvmul a d)) (bvmul c b)))))(check-sat)(exit)
EOF

  # AWS
  if [ ! -d "$BENCH_DIR/aws-c-common" ]; then
    echo "Downloading aws-c-common..."
    git clone --depth 1 https://github.com/awslabs/aws-c-common "$BENCH_DIR/aws-c-common" 2>&1 | tail -1
  fi

  # Bitwuzla
  if ! which bitwuzla >/dev/null 2>&1; then
    echo "Downloading Bitwuzla..."
    curl -sL -o /tmp/bitwuzla.zip "https://github.com/bitwuzla/bitwuzla/releases/download/0.9.0/Bitwuzla-Linux-x86_64-static.zip"
    unzip -o /tmp/bitwuzla.zip -d /tmp/bitwuzla-extract >/dev/null 2>&1
    sudo cp /tmp/bitwuzla-extract/Bitwuzla-Linux-x86_64-static/bin/bitwuzla /usr/local/bin/ 2>/dev/null || true
  fi
}

# ============================================================
# Build variants
# ============================================================
build_variant() {
  local name=$1 sat_impl=$2 cxx_flags=$3
  local build_dir="$BUILD_BASE/$name"
  local base_dir="$BUILD_BASE/base-${sat_impl}"

  if [ -x "$build_dir/bin/cbmc" ] && $SKIP_BUILD; then
    echo "  $name: reusing"
    return 0
  fi

  # Ensure base build exists
  if [ ! -x "$base_dir/bin/cbmc" ]; then
    echo -n "  Building base-${sat_impl}... "
    cmake -S "$ROOT_DIR" -B"$base_dir" -Dsat_impl="$sat_impl" \
      -DCMAKE_BUILD_TYPE=Release >/dev/null 2>&1
    cmake --build "$base_dir" --target cbmc smt2_solver -- -j$(nproc) >/dev/null 2>&1 \
      && echo "OK" || { echo "FAILED"; return 1; }
  fi

  # If no extra flags, just symlink to base
  if [ -z "$cxx_flags" ]; then
    if [ "$build_dir" != "$base_dir" ]; then
      rm -rf "$build_dir"
      ln -sf "$(basename "$base_dir")" "$build_dir"
    fi
    echo "  $name: = base-${sat_impl}"
    return 0
  fi

  # Copy base build and recompile only changed files
  if [ ! -d "$build_dir" ]; then
    cp -al "$base_dir" "$build_dir" 2>/dev/null || cp -r "$base_dir" "$build_dir"
  fi

  echo -n "  $name: recompile+relink... "

  # Extract compile commands from base build
  local bv_obj="src/solvers/CMakeFiles/solvers.dir/flattening/bv_utils.cpp.o"
  local ref_obj="src/solvers/CMakeFiles/solvers.dir/refinement/refine_arithmetic.cpp.o"

  # Get the compile command from the base build's ninja file and add our flags
  local bv_cmd=$(cd "$base_dir" && ninja -t commands "$bv_obj" 2>/dev/null | head -1)
  local ref_cmd=$(cd "$base_dir" && ninja -t commands "$ref_obj" 2>/dev/null | head -1)

  if [ -n "$bv_cmd" ]; then
    # Add our flags and redirect output to variant build dir
    (cd "$build_dir" && eval "${bv_cmd} ${cxx_flags}") >/dev/null 2>&1
    (cd "$build_dir" && eval "${ref_cmd} ${cxx_flags}") >/dev/null 2>&1

    # Relink solvers library and cbmc
    cmake --build "$build_dir" --target cbmc smt2_solver -- -j$(nproc) >/dev/null 2>&1 \
      && echo "OK" || echo "FAILED"
  else
    # Fallback: full cmake build with flags
    cmake -S "$ROOT_DIR" -B"$build_dir" -Dsat_impl="$sat_impl" \
      -DCMAKE_CXX_FLAGS="$cxx_flags" \
      -DCMAKE_BUILD_TYPE=Release >/dev/null 2>&1
    cmake --build "$build_dir" --target cbmc smt2_solver -- -j$(nproc) >/dev/null 2>&1 \
      && echo "OK" || echo "FAILED"
  fi
}

build_all() {
  mkdir -p "$BUILD_BASE"
  echo "=== Building CBMC variants ==="
  for enc_spec in "${ENCODINGS[@]}"; do
    local enc_name=${enc_spec%%:*}
    local enc_flags=${enc_spec##*:}
    for sat in "${SAT_SOLVERS[@]}"; do
      build_variant "${enc_name}-${sat}" "$sat" "$enc_flags"
    done
  done

  # Build refine-arithmetic variants (comba encoding, both SAT solvers)
  for refine_mode in 0 1 2 3; do
    for sat in "${SAT_SOLVERS[@]}"; do
      build_variant "comba-${sat}-refine${refine_mode}" "$sat" \
        "-DREFINE_MULT_MODE=${refine_mode}"
    done
  done
}

compile_aws_proofs() {
  local goto_cc="$BUILD_BASE/comba-cadical/bin/goto-cc"
  [ ! -x "$goto_cc" ] && goto_cc="$BUILD_BASE/baseline-cadical/bin/goto-cc"
  local outdir="$BENCH_DIR/aws-goto"
  [ -f "$outdir/aws_mul_size_checked.gb" ] && return 0
  mkdir -p "$outdir"
  local AWS="$BENCH_DIR/aws-c-common"
  local INC="-I $AWS/include -I $AWS/verification/cbmc/include"
  local DEF="-DCBMC -DCBMC_OBJECT_BITS=8 -DMAX_ITEM_SIZE=2 -DMAX_INITIAL_ITEM_ALLOCATION=9223372036854775808ULL -DMAX_BUFFER_SIZE=10"
  local COM="$AWS/source/allocator.c $AWS/source/common.c $AWS/source/error.c $AWS/verification/cbmc/sources/make_common_data_structures.c $AWS/verification/cbmc/sources/utils.c"
  for proof in aws_mul_size_checked aws_mul_size_saturating aws_add_size_checked aws_array_list_back aws_byte_buf_clean_up; do
    local h="$AWS/verification/cbmc/proofs/$proof/${proof}_harness.c"
    [ ! -f "$h" ] && continue
    local s="$h $COM"
    case $proof in aws_array_list*) s="$s $AWS/source/array_list.c";; aws_byte_buf*) s="$s $AWS/source/byte_buf.c";; esac
    echo -n "  $proof... "
    timeout 60 "$goto_cc" $INC $DEF $s --function ${proof}_harness -o "$outdir/${proof}.gb" 2>/dev/null && echo "OK" || echo "FAILED"
  done
}

# ============================================================
# Run benchmarks
# ============================================================
timed_run() {
  local cmd=$1 timeout_s=$2
  local total=0 ok=0
  for run in $(seq 1 $RUNS); do
    local out
    out=$(timeout "$timeout_s" /usr/bin/time -f 'TIME:%e' bash -c "$cmd" 2>&1)
    local t=$(echo "$out" | grep '^TIME:' | cut -d: -f2)
    local has_result=$(echo "$out" | grep -cE 'VERIFICATION (SUCCESSFUL|FAILED)|^(sat|unsat)$')
    if [ -n "$t" ] && [ "$has_result" -gt 0 ]; then
      total=$(echo "$total + $t" | bc)
      ok=1
    else
      total=$(echo "$total + $timeout_s" | bc)
    fi
  done
  local avg=$(echo "scale=2; $total / $RUNS" | bc)
  [ "$ok" != "1" ] && avg="${avg}!"
  echo "$avg"
}

run_all() {
  mkdir -p "$RESULTS_DIR"
  local csv="$RESULTS_DIR/results_$(date +%Y%m%d_%H%M%S).csv"
  echo "category,variant,benchmark,param,time_s" > "$csv"
  echo "=== Running benchmarks (timeout=${TIMEOUT}s, runs=$RUNS) ==="

  # Bitwidth specs per benchmark
  declare -A BW_SPECS
  BW_SPECS[comm]="7 9 11 13 15"
  BW_SPECS[distrib]="3 4 5 6 7"
  BW_SPECS[assoc]="3 5 7 9"
  BW_SPECS[const3]="8 16 32"
  BW_SPECS[factor]="8 12 16"
  BW_SPECS[square]="5 7 9 11"
  BW_SPECS[mul_overflow]="8 12 16"
  BW_SPECS[mul_shift]="8 16 32"
  BW_SPECS[mul_negation]="8 16 32"
  BW_SPECS[mul_double]="8 16 32"
  BW_SPECS[mul_bounds]="8 16 32"
  BW_SPECS[mul_zero_factor]="4 8 16"
  BW_SPECS[mul_square_nonneg]="8 16 32"
  if $QUICK; then
    BW_SPECS[comm]="7 9 11"
    BW_SPECS[distrib]="4 5"
    BW_SPECS[assoc]="5 7"
    BW_SPECS[factor]="8 12"
    BW_SPECS[square]="5 7"
    for k in mul_overflow mul_shift mul_negation mul_double mul_bounds mul_zero_factor mul_square_nonneg; do
      BW_SPECS[$k]="8 16"
    done
    BW_SPECS[const3]="8 16"
  fi

  # --- 1. Encoding × SAT solver variants on ALL synthetic benchmarks ---
  for variant_dir in "$BUILD_BASE"/*/; do
    local variant=$(basename "$variant_dir")
    local cbmc="$variant_dir/bin/cbmc"
    [ ! -x "$cbmc" ] && continue
    [[ "$variant" == *refine* ]] && continue  # handle separately

    echo ""
    echo "--- $variant ---"
    for bench in "${!BW_SPECS[@]}"; do
      for bw in ${BW_SPECS[$bench]}; do
        local t=$(timed_run "'$cbmc' '$BENCH_DIR/${bench}.c' -DBW=$bw --no-standard-checks --verbosity 4" "$TIMEOUT")
        local line="synth,$variant,$bench,BW=$bw,${t}s"
        echo "  $line"
        echo "$line" >> "$csv"
      done
    done

    # AWS proofs
    for gb in "$BENCH_DIR"/aws-goto/*.gb; do
      [ ! -f "$gb" ] && continue
      local name=$(basename "$gb" .gb)
      local t=$(timed_run "'$cbmc' '$gb' --unwind 10 --unwinding-assertions --verbosity 4" "$TIMEOUT")
      local line="aws,$variant,$name,unwind=10,${t}s"
      echo "  $line"
      echo "$line" >> "$csv"
    done
  done

  # --- 2. --refine-arithmetic variants (ALL benchmarks, both SAT solvers) ---
  for variant_dir in "$BUILD_BASE"/comba-*-refine*/; do
    local variant=$(basename "$variant_dir")
    local cbmc="$variant_dir/bin/cbmc"
    [ ! -x "$cbmc" ] && continue

    echo ""
    echo "--- $variant + refine ---"
    for bench in "${!BW_SPECS[@]}"; do
      for bw in ${BW_SPECS[$bench]}; do
        local t=$(timed_run "'$cbmc' '$BENCH_DIR/${bench}.c' -DBW=$bw --no-standard-checks --refine-arithmetic --verbosity 4" "$TIMEOUT")
        local line="synth,${variant}+refine,$bench,BW=$bw,${t}s"
        echo "  $line"
        echo "$line" >> "$csv"
      done
    done

    # AWS with refine
    for gb in "$BENCH_DIR"/aws-goto/*.gb; do
      [ ! -f "$gb" ] && continue
      local name=$(basename "$gb" .gb)
      local t=$(timed_run "'$cbmc' '$gb' --unwind 10 --unwinding-assertions --refine-arithmetic --verbosity 4" "$TIMEOUT")
      local line="aws,${variant}+refine,$name,unwind=10,${t}s"
      echo "  $line"
      echo "$line" >> "$csv"
    done
  done

  # --- 3. SMT solvers (one CBMC build, ALL synthetic benchmarks) ---
  local cbmc_smt="$BUILD_BASE/comba-cadical/bin/cbmc"
  if [ -x "$cbmc_smt" ]; then
    for solver_flag in "--z3" "--cvc5" "--bitwuzla"; do
      local sname=${solver_flag#--}
      # bitwuzla is invoked via CBMC, not as standalone binary
      if [ "$sname" != "bitwuzla" ]; then
        which "$sname" >/dev/null 2>&1 || continue
      fi
      echo ""
      echo "--- $sname ---"
      for bench in "${!BW_SPECS[@]}"; do
        for bw in ${BW_SPECS[$bench]}; do
          local t=$(timed_run "'$cbmc_smt' '$BENCH_DIR/${bench}.c' -DBW=$bw --no-standard-checks $solver_flag --verbosity 4" "$TIMEOUT")
          local line="synth,$sname,$bench,BW=$bw,${t}s"
          echo "  $line"
          echo "$line" >> "$csv"
        done
      done
    done
  fi

  # --- 4. SMT-COMP benchmarks via smt2_solver, z3, cvc5, bitwuzla ---
  echo ""
  echo "--- SMT-COMP benchmarks ---"
  local smt2_solver="$BUILD_BASE/comba-cadical/bin/smt2_solver"
  local smt_solvers=""
  [ -x "$smt2_solver" ] && smt_solvers="smt2_solver:$smt2_solver"
  which z3 >/dev/null 2>&1 && smt_solvers="$smt_solvers z3:z3"
  which cvc5 >/dev/null 2>&1 && smt_solvers="$smt_solvers cvc5:cvc5"
  if which bitwuzla >/dev/null 2>&1; then
    smt_solvers="$smt_solvers bitwuzla:bitwuzla bitwuzla-noabs:bitwuzla%--no-abstraction"
  fi

  for solver_spec in $smt_solvers; do
    local sname=${solver_spec%%:*}
    local scmd=${solver_spec#*:}
    scmd=${scmd//%/ }
    echo "  solver: $sname"
    for f in "$BENCH_DIR"/smt-comp/*.smt2; do
      local bname=$(basename "$f" .smt2)
      local t=$(timed_run "$scmd '$f'" "$TIMEOUT")
      local line="smt-comp,$sname,$bname,,${t}s"
      echo "  $line"
      echo "$line" >> "$csv"
    done
  done

  echo ""
  echo "=== Results: $csv ==="
  echo "=== $(grep -c ',' "$csv") data points ==="
}

# ============================================================
# Main
# ============================================================
create_benchmarks
if $DOWNLOAD_ONLY; then
  echo "Benchmarks ready."
  exit 0
fi
build_all
compile_aws_proofs
run_all
