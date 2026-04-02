#!/bin/bash
# Fetch benchmark sources for adder encoding evaluation.
# Downloads are cached — re-running skips already-fetched benchmarks.
#
# Usage: fetch_benchmarks.sh [benchmark_dir]

set -e
BENCH_DIR="${1:-$(dirname "$0")/benchmarks}"
mkdir -p "$BENCH_DIR"

log() { echo "[fetch] $*"; }

# ============================================================
# 1. Synthetic benchmarks (generated locally)
# ============================================================
SYNTH="$BENCH_DIR/synthetic"
if [ ! -f "$SYNTH/.done" ]; then
  log "Generating synthetic benchmarks..."
  mkdir -p "$SYNTH"

  cat > "$SYNTH/add_sat_200.c" << 'EOF'
// SAT: a[i]+b[i] > a[i] (trivially SAT via b<0)
#define N 200
int main() {
  int a[N], b[N];
  for(int i=0; i<N; ++i)
    __CPROVER_assert(a[i]+b[i] > a[i], "");
}
EOF

  cat > "$SYNTH/add_sat_2000.c" << 'EOF'
#define N 2000
int main() {
  int a[N], b[N];
  for(int i=0; i<N; ++i)
    __CPROVER_assert(a[i]+b[i] > a[i], "");
}
EOF

  cat > "$SYNTH/add_unsat_200.c" << 'EOF'
// UNSAT: constrained overflow check
#include <limits.h>
#define N 200
int main() {
  int a[N], b[N];
  for(int i=0; i<N; ++i)
    __CPROVER_assert(
      b[i] <= 0 ||
      (a[i] >= (INT_MAX >> 28) || b[i] >= (INT_MAX >> 28)) ||
      (a[i] <= (INT_MIN >> 1) || b[i] <= (INT_MIN >> 1)) ||
      a[i] + b[i] > a[i], "");
}
EOF

  cat > "$SYNTH/sub_sat_1000.c" << 'EOF'
// SAT: subtraction (hard for MiniSat)
#define N 1000
int main() {
  int a[N], b[N];
  for(int i=0; i<N; ++i)
    __CPROVER_assert(a[i] - b[i] < a[i], "");
}
EOF

  cat > "$SYNTH/equiv_unsat_100.c" << 'EOF'
// UNSAT: a+b == (a^b)+2*(a&b) (hard for all solvers)
#define N 100
int main() {
  unsigned a[N], b[N];
  for(int i=0; i<N; ++i) {
    unsigned sum1 = a[i] + b[i];
    unsigned sum2 = (a[i] ^ b[i]) + 2 * (a[i] & b[i]);
    __CPROVER_assert(sum1 == sum2, "");
  }
}
EOF

  cat > "$SYNTH/incr_sat_5000.c" << 'EOF'
// SAT: increment by constant
#define N 5000
int main() {
  int a[N];
  for(int i=0; i<N; ++i)
    __CPROVER_assert(a[i] + 1 != a[i], "");
}
EOF

  cat > "$SYNTH/wide_sat_1000.c" << 'EOF'
// SAT: 64-bit addition
#define N 1000
int main() {
  long long a[N], b[N];
  for(int i=0; i<N; ++i)
    __CPROVER_assert(a[i] + b[i] > a[i], "");
}
EOF

  cat > "$SYNTH/mixed_sat_500.c" << 'EOF'
// SAT: mixed add/sub/compare
#define N 500
int main() {
  int a[N], b[N], c[N];
  for(int i=0; i<N; ++i) {
    int sum = a[i] + b[i];
    int diff = a[i] - c[i];
    __CPROVER_assert(sum != diff || b[i] == -c[i] || a[i]+b[i] != a[i]-c[i], "");
  }
}
EOF

  cat > "$SYNTH/narrow_sat_10000.c" << 'EOF'
// SAT: 8-bit addition (many small adders)
#define N 10000
int main() {
  unsigned char a[N], b[N];
  for(int i=0; i<N; ++i)
    __CPROVER_assert((unsigned char)(a[i]+b[i]) >= a[i], "");
}
EOF

  cat > "$SYNTH/chain_sat_500.c" << 'EOF'
// SAT: chained additions a+b+c+d
#define N 500
int main() {
  int a[N], b[N], c[N], d[N];
  for(int i=0; i<N; ++i)
    __CPROVER_assert(a[i]+b[i]+c[i]+d[i] != 0, "");
}
EOF

  touch "$SYNTH/.done"
  log "Generated $(ls "$SYNTH"/*.c | wc -l) synthetic benchmarks"
else
  log "Synthetic benchmarks already present"
fi

# ============================================================
# 2. SMT2 benchmarks (generated locally)
# ============================================================
SMT="$BENCH_DIR/smt"
if [ ! -f "$SMT/.done" ]; then
  bash "$(dirname "$0")/gen_smt_benchmarks.sh" "$SMT"
  touch "$SMT/.done"
else
  log "SMT benchmarks already present ($(ls "$SMT"/*.smt2 2>/dev/null | wc -l) files)"
fi

# ============================================================
# 3. AWS C Common benchmarks
# ============================================================
AWS="$BENCH_DIR/aws-c-common"
if [ ! -f "$AWS/.done" ]; then
  log "Fetching AWS C Common verification harnesses..."
  mkdir -p "$AWS"

  if [ ! -d "$AWS/repo" ]; then
    git clone --depth 1 https://github.com/awslabs/aws-c-common.git "$AWS/repo" 2>&1 | tail -2
  fi

  # Extract a few arithmetic-heavy harnesses
  for harness in \
    "verification/cbmc/proofs/aws_add_size_checked/aws_add_size_checked_harness.c" \
    "verification/cbmc/proofs/aws_mul_size_checked/aws_mul_size_checked_harness.c"
  do
    name=$(basename "$harness" .c)
    if [ -f "$AWS/repo/$harness" ]; then
      cp "$AWS/repo/$harness" "$AWS/$name.c"
      log "  Extracted $name"
    fi
  done

  touch "$AWS/.done"
  log "AWS C Common benchmarks ready"
else
  log "AWS C Common benchmarks already present"
fi

# ============================================================
# 4. SV-COMP benchmarks
# ============================================================
SVCOMP="$BENCH_DIR/sv-comp"
if [ ! -f "$SVCOMP/.done" ]; then
  log "Fetching SV-COMP benchmarks..."
  mkdir -p "$SVCOMP"

  # Grab a few arithmetic-relevant benchmarks from sv-benchmarks
  SVCOMP_URL="https://raw.githubusercontent.com/sosy-lab/sv-benchmarks/main/c"
  for f in \
    "bitvector/jain_1_true-unreach-call.c" \
    "bitvector/jain_2_true-unreach-call.c" \
    "bitvector/jain_4_true-unreach-call.c" \
    "bitvector/jain_7_true-unreach-call.c"
  do
    name=$(basename "$f")
    if [ ! -f "$SVCOMP/$name" ]; then
      log "  Downloading $name..."
      curl -sL "$SVCOMP_URL/$f" -o "$SVCOMP/$name" 2>/dev/null || true
    fi
  done

  touch "$SVCOMP/.done"
  log "SV-COMP benchmarks ready"
else
  log "SV-COMP benchmarks already present"
fi

log "All benchmarks ready in $BENCH_DIR"
ls -la "$BENCH_DIR"/*/
