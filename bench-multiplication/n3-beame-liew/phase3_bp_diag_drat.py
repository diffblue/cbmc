#!/usr/bin/env python3
"""
N3 Phase 3 diagonal BP DRAT emission.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper_order import build_strip_all
from phase3_bp_diag import build_bp_diag
from phase3_bp_cut_drat import emit_tree_post_order_cut


def emit_drat_diag(n, k, out_path, cnf_path):
    cnf, strip_clauses, forced_e, delta = build_strip_all(n, k)
    bp = build_bp_diag(n, k)

    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, "w") as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(" ".join(str(l) for l in cl) + " 0\n")

    with open(out_path, "w") as f:
        if bp.get("conflict") is not None:
            f.write("0\n")
        else:
            emit_tree_post_order_cut(bp, f)


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_diag_drat.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])
    cnf_path = f"/tmp/strip_diag_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_diag_n{n}_k{k}.drat"
    emit_drat_diag(n, k, drat_path, cnf_path)

    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n}, k={k}: CNF {cnf_bytes}B, DRAT {drat_bytes}B ({drat_lines} lemmas)")

    import subprocess
    result = subprocess.run(
        ["/tmp/drat-trim", cnf_path, drat_path],
        capture_output=True, text=True, timeout=180,
    )
    for line in result.stdout.split("\n"):
        if line.startswith("s "):
            print(f"  {line}")


if __name__ == "__main__":
    main()
