#!/bin/bash
# Distributivity scaling: a*(b+c) == a*b + a*c through stored intermediates,
# at varying operand bit-widths.
set -u
TMP=/tmp/scaling_dist
mkdir -p $TMP
CBMC=/home/ubuntu/cbmc-github.git/build/bin/cbmc
TIMEOUT=180
OUTFILE=/home/ubuntu/cbmc-github.git/bench-multiplication/scaling-distributivity.tsv

ulimit -v 57591731 2>/dev/null

# (W, IN, OUT) — cast prevents simplifier from trivialising
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
  "32:uint32_t:uint64_t"
)

emit_distrib() {
  local W=$1; local IN=$2; local OUT=$3
  cat > $TMP/dist_${W}.c <<EOF
#include <stdint.h>
$OUT store($OUT x) { return x; }
int main() { $IN a, b, c;
  $OUT lhs = store(($OUT)a * (($OUT)b + ($OUT)c));
  $OUT rhs = store(($OUT)a * ($OUT)b) + store(($OUT)a * ($OUT)c);
  __CPROVER_assert(lhs == rhs, "");
  return 0; }
EOF
}

run_one() {
  local file=$1; local toggle=$2
  rt=$( { time -p timeout $TIMEOUT env $toggle $CBMC $file --refine-arithmetic --no-standard-checks >/tmp/sc.log 2>&1; } 2>&1 | grep -oE "real [0-9.]+" | awk '{print $2}')
  ver=$(grep -oE "VERIFICATION SUCCESSFUL|VERIFICATION FAILED" /tmp/sc.log | head -1)
  dist=$(grep -oE "[0-9]+ distributive" /tmp/sc.log | grep -oE "[0-9]+" | head -1)
  if [ -z "$ver" ]; then echo "TIMEOUT|0"
  else echo "${rt}|${dist:-0}"; fi
}

echo -e "w\twith_s\twith_dist_triples\twithout_s\tratio" | tee $OUTFILE
for entry in "${PATTERNS[@]}"; do
  W=${entry%%:*}; rest=${entry#*:}; IN=${rest%%:*}; OUT=${rest#*:}
  emit_distrib $W "$IN" "$OUT"
  file=$TMP/dist_${W}.c
  with_info=$(run_one "$file" "")
  without_info=$(run_one "$file" "CBMC_DISABLE_REFINE_PAIR_DETECTION=1")
  with=${with_info%|*}; dist=${with_info#*|}
  without=${without_info%|*}
  if [[ "$without" == "TIMEOUT" || "$with" == "TIMEOUT" ]]; then ratio="-"
  else ratio=$(echo "scale=1; $without / $with" | bc 2>/dev/null || echo "-"); fi
  echo -e "${W}\t${with}\t${dist}\t${without}\t${ratio}" | tee -a $OUTFILE
done
echo "Saved to $OUTFILE"
