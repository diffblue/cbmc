#!/bin/bash
# Analyze proof traces to extract solver statistics.
# Usage: analyze_proof.sh <cnf_file> [num_seeds]

set -e
CBMC_DIR=$(cd "$(dirname "$0")/../.." && pwd)
CADICAL=$CBMC_DIR/build/cadical-src/build/cadical
CNF=$1
SEEDS=${2:-3}

if [ -z "$CNF" ]; then
  echo "Usage: $0 <cnf_file> [num_seeds]"
  exit 1
fi

echo "=== Proof Analysis: $(basename $CNF) ==="
echo "Formula: $(head -1 $CNF)"
echo ""

# Run multiple seeds, collect universal learned clauses
for seed in $(seq 1 $SEEDS); do
  proof=/tmp/proof_analysis_s${seed}.txt
  ulimit -v 8000000
  timeout 120 $CADICAL "$CNF" --no-binary --seed=$seed "$proof" 2>&1 | \
    grep "conflicts:\|decisions:\|propagations:\|eliminated:" | head -4
  echo "  Proof: $(grep -cv '^d ' "$proof") learned, $(grep -c '^d ' "$proof") deleted"

  # Extract binary learned clauses
  grep -v '^d ' "$proof" | \
    awk 'NF==3 && $3==0 {a=$1;b=$2; if(a>b){t=a;a=b;b=t} print a,b}' | \
    sort -u > /tmp/proof_bin_s${seed}.txt
  echo "  Binary learned: $(wc -l < /tmp/proof_bin_s${seed}.txt)"
  echo ""
done

# Find universal clauses
if [ $SEEDS -ge 2 ]; then
  result=/tmp/proof_bin_s1.txt
  for seed in $(seq 2 $SEEDS); do
    comm -12 <(sort "$result") <(sort /tmp/proof_bin_s${seed}.txt) > /tmp/proof_universal_tmp.txt
    cp /tmp/proof_universal_tmp.txt "$result"
  done
  cp "$result" /tmp/proof_universal_final.txt

  max_var=$(head -1 "$CNF" | awk '{print $3}')
  awk -v max=$max_var '{
    a=$1;b=$2;
    if(a<0)aa=-a;else aa=a;
    if(b<0)bb=-b;else bb=b;
    if(aa<=max && bb<=max) print
  }' /tmp/proof_universal_final.txt > /tmp/proof_universal_filtered.txt

  echo "=== Universal Binary Clauses ==="
  echo "Total: $(wc -l < /tmp/proof_universal_final.txt)"
  echo "Filtered (original vars only): $(wc -l < /tmp/proof_universal_filtered.txt)"
  echo ""

  # Test speedup from adding universal clauses
  orig_clauses=$(head -1 "$CNF" | awk '{print $4}')
  extra=$(wc -l < /tmp/proof_universal_filtered.txt)
  new_clauses=$((orig_clauses + extra))

  cp "$CNF" /tmp/proof_augmented.cnf
  sed -i "1s/.*/p cnf $max_var $new_clauses/" /tmp/proof_augmented.cnf
  awk '{print $1, $2, "0"}' /tmp/proof_universal_filtered.txt >> /tmp/proof_augmented.cnf

  echo "=== Speedup from Universal Lemma Injection ==="
  echo -n "Original:  "
  ulimit -v 8000000 && timeout 120 $CADICAL "$CNF" 2>&1 | grep "total process time"
  echo -n "Augmented: "
  ulimit -v 8000000 && timeout 120 $CADICAL /tmp/proof_augmented.cnf 2>&1 | grep "total process time"
fi

# Cleanup
rm -f /tmp/proof_analysis_s*.txt /tmp/proof_bin_s*.txt /tmp/proof_universal_*.txt /tmp/proof_augmented.cnf
