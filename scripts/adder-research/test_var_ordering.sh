#!/bin/bash
# Test the effect of variable ordering on solver performance.
# Renumbers variables in a DIMACS file according to different strategies
# and measures the impact on solving time.
#
# Usage: test_var_ordering.sh <cnf_file> [timeout]

set -e
CBMC_DIR=$(cd "$(dirname "$0")/../.." && pwd)
CADICAL=$CBMC_DIR/build/cadical-src/build/cadical
CNF=$1
TIMEOUT=${2:-60}

if [ -z "$CNF" ]; then
  echo "Usage: $0 <cnf_file> [timeout]"
  exit 1
fi

echo "=== Variable Ordering Experiment ==="
echo "Input: $(head -1 $CNF)"
echo ""

# Extract variable info from DIMACS comments
# CBMC names variables: inputs get low numbers, Tseitin aux get higher
# We'll test: original, reversed, inputs-first, aux-first, random

MAX_VAR=$(head -1 "$CNF" | awk '{print $3}')

# Identify "input" variables (named in comments) vs auxiliary
grep "^c " "$CNF" | awk '{for(i=3;i<=NF;i++) if($i+0>0) print $i}' | \
  sort -nu > /tmp/vo_named.txt
NAMED=$(wc -l < /tmp/vo_named.txt)
echo "Named (input/output) variables: $NAMED of $MAX_VAR"
echo ""

run_with_ordering() {
  local label=$1
  local mapping_file=$2  # file with: old_var new_var

  if [ "$mapping_file" = "IDENTITY" ]; then
    cp "$CNF" /tmp/vo_reordered.cnf
  else
    # Apply variable renumbering
    python3 - "$CNF" "$mapping_file" /tmp/vo_reordered.cnf << 'PYEOF'
import sys
cnf_file, map_file, out_file = sys.argv[1], sys.argv[2], sys.argv[3]

# Read mapping
mapping = {}
with open(map_file) as f:
    for line in f:
        old, new = line.strip().split()
        mapping[int(old)] = int(new)

def remap(lit):
    if lit == 0: return 0
    v = abs(lit)
    nv = mapping.get(v, v)
    return nv if lit > 0 else -nv

with open(cnf_file) as fin, open(out_file, 'w') as fout:
    for line in fin:
        if line.startswith('c') or line.startswith('p'):
            fout.write(line)
        else:
            lits = [remap(int(x)) for x in line.strip().split()]
            fout.write(' '.join(str(l) for l in lits) + '\n')
PYEOF
  fi

  # Run CaDiCaL
  local out=$(ulimit -v 8000000; timeout $TIMEOUT $CADICAL /tmp/vo_reordered.cnf 2>&1)
  local time=$(echo "$out" | grep "total process time" | sed 's/.*: *//;s/ .*//')
  local conflicts=$(echo "$out" | grep "^c conflicts:" | sed 's/.*: *\([0-9]*\).*/\1/')
  local decisions=$(echo "$out" | grep "^c decisions:" | sed 's/.*: *\([0-9]*\).*/\1/')
  local props=$(echo "$out" | grep "^c propagations:" | sed 's/.*: *\([0-9]*\).*/\1/')
  [ -z "$time" ] && time="T/O"
  printf "%-25s time=%-8s conflicts=%-8s decisions=%-10s props=%s\n" \
    "$label" "$time" "$conflicts" "$decisions" "$props"
}

# 1. Original ordering
run_with_ordering "Original" "IDENTITY"

# 2. Reversed: high-numbered vars become low-numbered
awk -v max=$MAX_VAR 'BEGIN{for(i=1;i<=max;i++) print i, max-i+1}' > /tmp/vo_reversed.txt
run_with_ordering "Reversed" /tmp/vo_reversed.txt

# 3. Named (inputs) first: give named variables numbers 1..N,
#    auxiliary variables get N+1..MAX
python3 - /tmp/vo_named.txt $MAX_VAR /tmp/vo_inputs_first.txt << 'PYEOF'
import sys
named_file, max_var_str = sys.argv[1], sys.argv[2]
max_var = int(max_var_str)
named = set()
with open(named_file) as f:
    for line in f:
        named.add(int(line.strip()))
# Named vars get 1..len(named), aux get len(named)+1..max_var
mapping = {}
next_named = 1
next_aux = len(named) + 1
for v in range(1, max_var + 1):
    if v in named:
        mapping[v] = next_named
        next_named += 1
    else:
        mapping[v] = next_aux
        next_aux += 1
with open(sys.argv[3], 'w') as f:
    for old, new in sorted(mapping.items()):
        f.write(f"{old} {new}\n")
PYEOF
run_with_ordering "Inputs first" /tmp/vo_inputs_first.txt

# 4. Auxiliary first: give aux variables numbers 1..M,
#    named variables get M+1..MAX
python3 - /tmp/vo_named.txt $MAX_VAR /tmp/vo_aux_first.txt << 'PYEOF'
import sys
named_file, max_var_str = sys.argv[1], sys.argv[2]
max_var = int(max_var_str)
named = set()
with open(named_file) as f:
    for line in f:
        named.add(int(line.strip()))
mapping = {}
next_aux = 1
next_named = max_var - len(named) + 1
for v in range(1, max_var + 1):
    if v in named:
        mapping[v] = next_named
        next_named += 1
    else:
        mapping[v] = next_aux
        next_aux += 1
with open(sys.argv[3], 'w') as f:
    for old, new in sorted(mapping.items()):
        f.write(f"{old} {new}\n")
PYEOF
run_with_ordering "Aux (Tseitin) first" /tmp/vo_aux_first.txt

# 5. Random permutation
python3 -c "
import random; random.seed(42)
n = $MAX_VAR
perm = list(range(1, n+1))
random.shuffle(perm)
for i, p in enumerate(perm):
    print(i+1, p)
" > /tmp/vo_random.txt
run_with_ordering "Random" /tmp/vo_random.txt

# Cleanup
rm -f /tmp/vo_*.txt /tmp/vo_*.cnf
