#!/bin/bash
# Compare two benchmark result sets and produce a summary.
#
# Usage: compare_results.sh <results_csv_A> <results_csv_B>

set -e

if [ $# -lt 2 ]; then
  echo "Usage: $0 <results_A.csv> <results_B.csv>"
  exit 1
fi

python3 - "$1" "$2" << 'PYEOF'
import sys, csv
from collections import defaultdict
import statistics

def load(path):
    data = defaultdict(list)
    config = None
    with open(path) as f:
        reader = csv.DictReader(f)
        for row in reader:
            config = row['config']
            key = row['benchmark']
            t = row['solver_time_s']
            if t and t != 'T/O':
                data[key].append(float(t))
            else:
                data[key].append(None)
    return config, data

config_a, data_a = load(sys.argv[1])
config_b, data_b = load(sys.argv[2])

all_benchmarks = sorted(set(data_a.keys()) | set(data_b.keys()))

print(f"Comparison: {config_a} vs {config_b}")
print(f"{'Benchmark':<25} {config_a:>12} {config_b:>12} {'Speedup':>10} {'Status':>8}")
print("-" * 75)

wins = losses = ties = 0
for bench in all_benchmarks:
    times_a = [t for t in data_a.get(bench, []) if t is not None]
    times_b = [t for t in data_b.get(bench, []) if t is not None]

    if times_a:
        mean_a = statistics.mean(times_a)
        str_a = f"{mean_a:.4f}s"
    else:
        mean_a = None
        str_a = "T/O"

    if times_b:
        mean_b = statistics.mean(times_b)
        str_b = f"{mean_b:.4f}s"
    else:
        mean_b = None
        str_b = "T/O"

    if mean_a and mean_b:
        speedup = mean_a / mean_b
        if speedup > 1.05:
            status = "FASTER"
            wins += 1
        elif speedup < 0.95:
            status = "SLOWER"
            losses += 1
        else:
            status = "~same"
            ties += 1
        str_sp = f"{speedup:.2f}x"
    elif mean_a and not mean_b:
        str_sp = "B=T/O"
        status = "SLOWER"
        losses += 1
    elif not mean_a and mean_b:
        str_sp = "A=T/O"
        status = "FASTER"
        wins += 1
    else:
        str_sp = "both T/O"
        status = "~same"
        ties += 1

    print(f"{bench:<25} {str_a:>12} {str_b:>12} {str_sp:>10} {status:>8}")

print("-" * 75)
print(f"Summary: {wins} faster, {losses} slower, {ties} same")
print(f"  (B is faster when speedup > 1.0)")
PYEOF
