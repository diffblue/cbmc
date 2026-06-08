#!/bin/bash
# Comparison study: pair detection vs alternatives.
# Output: bench-multiplication/comparison-study.tsv
set -u
ROOT=$(realpath "$(dirname "$0")/..")
cd "$ROOT"
CBMC=$ROOT/build/bin/cbmc
TIMEOUT=30
OUTFILE=$ROOT/bench-multiplication/comparison-study.tsv

ulimit -v 57591731 2>/dev/null || true

# Optional alternative solvers
BITWUZLA=/home/ubuntu/bitwuzla.git/build/src/main/bitwuzla
CMS=/usr/bin/cryptominisat5

run_cell() {
  local test=$1; local mode=$2
  local prefix=""; local extra=""
  case $mode in
    default)        ;;
    refine_pair)    extra="--refine-arithmetic" ;;
    refine_no_pair) extra="--refine-arithmetic"; prefix="env CBMC_DISABLE_REFINE_PAIR_DETECTION=1" ;;
    xor_gauss)      extra="--xor-gauss" ;;
    cms)            [ -x "$CMS" ] || { echo "skip"; return; }
                    extra="--external-sat-solver $CMS" ;;
    bitwuzla)       [ -x "$BITWUZLA" ] || { echo "skip"; return; }
                    extra="--incremental-smt2-solver $BITWUZLA" ;;
  esac
  rt=$( { time -p timeout $TIMEOUT $prefix $CBMC $test --no-standard-checks $extra >/tmp/c.log 2>&1; } 2>&1 | grep -oE "real [0-9.]+" | awk '{print $2}')
  ver=$(grep -oE "VERIFICATION SUCCESSFUL|VERIFICATION FAILED" /tmp/c.log | head -1)
  if [ -z "$ver" ]; then echo "T/O"; else echo "$rt"; fi
}

cat > "$OUTFILE" <<HEADER
# Comparison study: pair detection vs alternatives
# Time in seconds; T/O = $TIMEOUT s timeout
benchmark	cbmc_default	cbmc_refine_pair	cbmc_refine_no_pair	cbmc_xor_gauss	cryptominisat	bitwuzla
HEADER

# Synthetic stored patterns
[ -f /tmp/stored_comm.c ] || cat > /tmp/stored_comm.c <<EOF
#include <stdint.h>
uint64_t store(uint64_t x) { return x; }
int main() { uint16_t a, b;
  uint64_t p = store((uint64_t)a*(uint64_t)b);
  uint64_t q = store((uint64_t)b*(uint64_t)a);
  __CPROVER_assert(p == q, ""); return 0; }
EOF

[ -f /tmp/stored_comm32.c ] || cat > /tmp/stored_comm32.c <<EOF
#include <stdint.h>
typedef unsigned long long u64;
u64 store(u64 x) { return x; }
int main() { uint32_t a, b;
  u64 p = store((u64)a*(u64)b);
  u64 q = store((u64)b*(u64)a);
  __CPROVER_assert(p == q, ""); return 0; }
EOF

[ -f /tmp/sub_comm.c ] || cat > /tmp/sub_comm.c <<EOF
#include <stdint.h>
int main() { uint16_t a, b;
  uint16_t diff = (uint16_t)(a*b) - (uint16_t)(b*a);
  __CPROVER_assert(diff == 0, ""); return 0; }
EOF

[ -f /tmp/assoc_stored.c ] || cat > /tmp/assoc_stored.c <<EOF
#include <stdint.h>
uint64_t store(uint64_t x) { return x; }
int main() { uint16_t a, b, c;
  uint64_t ab = store((uint64_t)a*(uint64_t)b);
  uint64_t left = store(ab*(uint64_t)c);
  uint64_t bc = store((uint64_t)b*(uint64_t)c);
  uint64_t right = store((uint64_t)a*bc);
  __CPROVER_assert(left == right, ""); return 0; }
EOF

[ -f /tmp/distrib_simple.c ] || cat > /tmp/distrib_simple.c <<EOF
#include <stdint.h>
uint64_t store(uint64_t x) { return x; }
int main() { uint16_t a, b, c;
  uint64_t lhs = store((uint64_t)a*((uint64_t)b+(uint64_t)c));
  uint64_t rhs = store((uint64_t)a*(uint64_t)b)+store((uint64_t)a*(uint64_t)c);
  __CPROVER_assert(lhs == rhs, ""); return 0; }
EOF

for test in /tmp/stored_comm.c /tmp/stored_comm32.c /tmp/sub_comm.c /tmp/assoc_stored.c \
            /tmp/distrib_simple.c bench-multiplication/widen_mul.c bench-multiplication/mod_mul.c \
            bench-multiplication/comm.c bench-multiplication/distrib.c bench-multiplication/assoc.c \
            bench-multiplication/hash_mul.c bench-multiplication/mac_equiv.c \
            bench-multiplication/matrix_mul.c bench-multiplication/matrix_trace_16.c; do
  [ -f "$test" ] || continue
  name=$(basename "$test" .c)
  d=$(run_cell "$test" default)
  rp=$(run_cell "$test" refine_pair)
  rn=$(run_cell "$test" refine_no_pair)
  xg=$(run_cell "$test" xor_gauss)
  cms_t=$(run_cell "$test" cms)
  bw=$(run_cell "$test" bitwuzla)
  printf "%-22s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$name" "$d" "$rp" "$rn" "$xg" "$cms_t" "$bw" | tee -a "$OUTFILE"
done
echo "Saved to $OUTFILE"
