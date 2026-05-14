#!/bin/bash
# Final scaling study covering small-to-large widths.
set -u
TMP=/tmp/scaling_final
mkdir -p $TMP
CBMC=/home/ubuntu/cbmc-github.git/build/bin/cbmc
TIMEOUT=180
OUT=/home/ubuntu/cbmc-github.git/bench-multiplication/scaling-pair-detection.tsv

ulimit -v 57591731 2>/dev/null

# (W, IN, OUT) — IN must be narrower than OUT for the simplifier
# not to trivialise via expression-level commutativity. We use
# __CPROVER_bitvector[W] for non-power-of-two widths to get exact W bits.
PATTERNS=(
  "4:__CPROVER_bitvector[4]:uint16_t"
  "6:__CPROVER_bitvector[6]:uint16_t"
  "8:uint8_t:uint16_t"
  "10:__CPROVER_bitvector[10]:uint32_t"
  "12:__CPROVER_bitvector[12]:uint32_t"
  "14:__CPROVER_bitvector[14]:uint32_t"
  "16:uint16_t:uint32_t"
  "20:__CPROVER_bitvector[20]:uint64_t"
  "24:__CPROVER_bitvector[24]:uint64_t"
  "28:__CPROVER_bitvector[28]:uint64_t"
  "32:uint32_t:uint64_t"
)

emit_widen_mul() {
  local W=$1; local IN=$2; local OUT=$3
  cat > $TMP/widen_${W}.c <<EOF
#include <stdint.h>
int main() { $IN a, b;
  $OUT p = ($OUT)a * ($OUT)b;
  $OUT q = ($OUT)b * ($OUT)a;
  __CPROVER_assert(p == q, "");
  return 0; }
EOF
}

emit_stored_widen() {
  local W=$1; local IN=$2; local OUT=$3
  cat > $TMP/stored_${W}.c <<EOF
#include <stdint.h>
$OUT store($OUT x) { return x; }
int main() { $IN a, b;
  $OUT p = store(($OUT)a * ($OUT)b);
  $OUT q = store(($OUT)b * ($OUT)a);
  __CPROVER_assert(p == q, "");
  return 0; }
EOF
}

emit_three_term_widen() {
  local W=$1; local IN=$2; local OUT=$3
  cat > $TMP/three_${W}.c <<EOF
#include <stdint.h>
int main() { $IN a, b, c, x, y, z;
  $OUT s1 = ($OUT)a*($OUT)x + ($OUT)b*($OUT)y + ($OUT)c*($OUT)z;
  $OUT s2 = ($OUT)y*($OUT)b + ($OUT)z*($OUT)c + ($OUT)x*($OUT)a;
  __CPROVER_assert(s1 == s2, "");
  return 0; }
EOF
}

emit_assoc_widen() {
  local W=$1; local IN=$2; local OUT=$3
  cat > $TMP/assoc_${W}.c <<EOF
#include <stdint.h>
$OUT store($OUT x) { return x; }
int main() { $IN a, b, c;
  $OUT ab = store(($OUT)a * ($OUT)b);
  $OUT left = store(ab * ($OUT)c);
  $OUT bc = store(($OUT)b * ($OUT)c);
  $OUT right = store(($OUT)a * bc);
  __CPROVER_assert(left == right, "");
  return 0; }
EOF
}

run_one() {
  local file=$1; local toggle=$2
  rt=$( { time -p timeout $TIMEOUT env $toggle $CBMC $file --refine-arithmetic --no-standard-checks >/tmp/sc.log 2>&1; } 2>&1 | grep -oE "real [0-9.]+" | awk '{print $2}')
  ver=$(grep -oE "VERIFICATION SUCCESSFUL|VERIFICATION FAILED" /tmp/sc.log | head -1)
  pairs=$(grep -oE "[0-9]+ commutative/associative" /tmp/sc.log | grep -oE "[0-9]+" | head -1)
  if [ -z "$ver" ]; then echo "TIMEOUT|0"
  elif [ -z "$rt" ]; then echo "ERR|0"
  else echo "${rt}|${pairs:-0}"; fi
}

# Header
echo -e "pattern\tw\twith_s\twith_pairs\twithout_s\tratio" | tee $OUT

for emit_fn in emit_widen_mul emit_stored_widen emit_three_term_widen emit_assoc_widen; do
  pattern=${emit_fn#emit_}
  for entry in "${PATTERNS[@]}"; do
    W=${entry%%:*}; rest=${entry#*:}; IN=${rest%%:*}; OUT=${rest#*:}
    case $emit_fn in
      emit_widen_mul)        emit_widen_mul $W "$IN" "$OUT"; file=$TMP/widen_${W}.c ;;
      emit_stored_widen)     emit_stored_widen $W "$IN" "$OUT"; file=$TMP/stored_${W}.c ;;
      emit_three_term_widen) emit_three_term_widen $W "$IN" "$OUT"; file=$TMP/three_${W}.c ;;
      emit_assoc_widen)      emit_assoc_widen $W "$IN" "$OUT"; file=$TMP/assoc_${W}.c ;;
    esac
    with_info=$(run_one "$file" "")
    without_info=$(run_one "$file" "CBMC_DISABLE_REFINE_PAIR_DETECTION=1")
    with=${with_info%|*}; pairs=${with_info#*|}
    without=${without_info%|*}
    if [[ "$without" == "TIMEOUT" || "$with" == "TIMEOUT" ]]; then ratio="-"
    else ratio=$(echo "scale=1; $without / $with" | bc 2>/dev/null || echo "-"); fi
    echo -e "${pattern}\t${W}\t${with}\t${pairs}\t${without}\t${ratio}" | tee -a $OUT
  done
done
echo "Saved to scaling-pair-detection.tsv"
