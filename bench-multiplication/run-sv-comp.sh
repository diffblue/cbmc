#!/bin/bash
# SV-COMP sample A/B for pair detection (categories that may have
# multiplication).
# Output: bench-multiplication/sv-comp-results.tsv
set -u
ROOT=$(realpath "$(dirname "$0")/..")
cd "$ROOT"
CBMC=$ROOT/build/bin/cbmc
TIMEOUT=10
SAMPLE=30
SVDIR=/tmp/sv-bv
OUTFILE=$ROOT/bench-multiplication/sv-comp-results.tsv

ulimit -v 57591731 2>/dev/null || true

if [ ! -d "$SVDIR/c/bitvector" ]; then
  echo "ERROR: $SVDIR not present. To populate:"
  echo "  cd /tmp && git clone --depth=1 --filter=blob:none --sparse https://github.com/sosy-lab/sv-benchmarks.git sv-bv"
  echo "  cd /tmp/sv-bv && git sparse-checkout add c/bitvector c/loops c/float-newlib"
  exit 1
fi

cat > "$OUTFILE" <<HEADER
# SV-COMP sample results: pair detection hit rate
# Sampled with --refine-arithmetic --no-standard-checks, ${TIMEOUT} s timeout, ${SAMPLE} files per category
category	files_sampled	pairs_fired	helped	hurt	same
HEADER

for category in bitvector loops float-newlib; do
  cat_dir="$SVDIR/c/$category"
  [ -d "$cat_dir" ] || continue
  
  total=0; pairs_fired=0; helped=0; hurt=0; same=0
  for f in $(ls "$cat_dir"/*.c 2>/dev/null | shuf -n $SAMPLE); do
    total=$((total+1))
    
    timeout $TIMEOUT $CBMC "$f" --refine-arithmetic --no-standard-checks --unwind 5 >/tmp/svc.log 2>&1
    ver_w=$(grep -oE "VERIFICATION SUCCESSFUL|VERIFICATION FAILED|PARSING ERROR" /tmp/svc.log | head -1)
    pairs=$(grep -oE "[0-9]+ commutative" /tmp/svc.log | head -1)
    
    timeout $TIMEOUT env CBMC_DISABLE_REFINE_PAIR_DETECTION=1 $CBMC "$f" --refine-arithmetic --no-standard-checks --unwind 5 >/tmp/svc2.log 2>&1
    ver_n=$(grep -oE "VERIFICATION SUCCESSFUL|VERIFICATION FAILED|PARSING ERROR" /tmp/svc2.log | head -1)
    
    if [ -n "$pairs" ]; then pairs_fired=$((pairs_fired+1)); fi
    [ "$ver_w" = "PARSING ERROR" ] && continue
    
    if [ -z "$ver_w" ] && [ -n "$ver_n" ]; then hurt=$((hurt+1))
    elif [ -n "$ver_w" ] && [ -z "$ver_n" ]; then helped=$((helped+1))
    else same=$((same+1)); fi
  done
  echo -e "${category}\t${total}\t${pairs_fired}\t${helped}\t${hurt}\t${same}" | tee -a "$OUTFILE"
done
echo "Saved to $OUTFILE"
