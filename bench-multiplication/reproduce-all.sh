#!/bin/bash
# Reproduce all data tables for the pair-detection writeup.
# Total wall-clock: ~30-60 min on a modern machine.
#
# Usage:
#   bash bench-multiplication/reproduce-all.sh
# Prerequisites:
#   - CBMC built at ./build/bin/cbmc
#   - bash, time, bc, perl
# Optional:
#   - Bitwuzla at /home/ubuntu/bitwuzla.git/build/src/main/bitwuzla
#   - CryptoMiniSat5 at /usr/bin/cryptominisat5
#   - SV-COMP checkout at /tmp/sv-bv (sparse: c/bitvector, c/loops, c/float-newlib)

set -u

ROOT=$(realpath "$(dirname "$0")/..")
cd "$ROOT"

CBMC=$ROOT/build/bin/cbmc
if [ ! -x "$CBMC" ]; then
  echo "ERROR: $CBMC not found. Run 'cmake --build build --target cbmc' first." >&2
  exit 1
fi

ulimit -v 57591731 2>/dev/null || true

echo "=================================================================="
echo "Reproducing pair-detection experiments. Output goes to:"
echo "  - bench-multiplication/{scaling-pair-detection,scaling-distributivity}.tsv"
echo "  - bench-multiplication/comparison-study.tsv"
echo "  - bench-multiplication/{sv-comp,auto-large}-results.tsv"
echo "  - bench-multiplication/realistic-patterns/results.tsv"
echo "=================================================================="

echo
echo "--- 1. Scaling: commutative/associative patterns (~5 min) ---"
bash bench-multiplication/run-pair-detection-scaling.sh

echo
echo "--- 2. Scaling: distributivity (~5 min) ---"
bash bench-multiplication/run-distributivity-scaling.sh

echo
echo "--- 3. Comparison study (~5 min) ---"
bash bench-multiplication/run-comparison-study.sh

echo
echo "--- 4. Realistic patterns (~5 min, p1 takes 5+ min if you wait) ---"
bash bench-multiplication/run-realistic-patterns.sh

echo
echo "--- 5. Auto-large benchmarks (~3 min) ---"
bash bench-multiplication/run-auto-large.sh

echo
echo "--- 6. SV-COMP sample (only if /tmp/sv-bv is populated) ---"
if [ -d /tmp/sv-bv/c/bitvector ]; then
  bash bench-multiplication/run-sv-comp.sh
else
  echo "  /tmp/sv-bv not found; skipping. To populate:"
  echo "    cd /tmp && git clone --depth=1 --filter=blob:none --sparse https://github.com/sosy-lab/sv-benchmarks.git sv-bv"
  echo "    cd /tmp/sv-bv && git sparse-checkout add c/bitvector c/loops c/float-newlib"
fi

echo
echo "All done."
