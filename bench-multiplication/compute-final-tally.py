import csv

pools = [
    ("C-input pool", "bench-multiplication/wide-three-approach-comparison.tsv", 5),
    ("SMT2 algebraic-identity pool", "bench-multiplication/wide-smt2-five-approach.tsv", 5),
    ("SMT-COMP real-world pool", "bench-multiplication/wide-smt-comp-five-approach.tsv", 5),
]

print(f"{'Pool':40} {'shift':>6} {'comba':>6} {'pair':>6} {'p2_alg':>6} {'all':>6} {'union':>6} {'total':>6}")
total_solved = [0]*5
total_union = 0
total_total = 0
for name, path, _ in pools:
    with open(path) as f:
        rows = [line.strip().split('\t') for line in f if not line.startswith('#') and not line.startswith('benchmark')]
    rows = [r for r in rows if len(r) >= 6]
    counts = [sum(1 for r in rows if r[i+1] != "T/O") for i in range(5)]
    union = sum(1 for r in rows if any(r[i+1] != "T/O" for i in range(5)))
    print(f"{name:40} {counts[0]:>6} {counts[1]:>6} {counts[2]:>6} {counts[3]:>6} {counts[4]:>6} {union:>6} {len(rows):>6}")
    for i in range(5):
        total_solved[i] += counts[i]
    total_union += union
    total_total += len(rows)

print("-" * 95)
print(f"{'TOTAL':40} {total_solved[0]:>6} {total_solved[1]:>6} {total_solved[2]:>6} {total_solved[3]:>6} {total_solved[4]:>6} {total_union:>6} {total_total:>6}")
