#!/usr/bin/env python3
"""
N3 Phase 3 step 2 v8: emit ALL BP paths (unfolding the DAG to tree).

Each path from root to a leaf gives one cut clause. Cuts may
coincide for distinct paths, in which case we emit the cut once
but still "count" it multiple times for resolution.

This is like v6 but without collapsing duplicate paths before
emission.
"""

import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper_order import (
    build_bp, build_strip_all, propagate,
)


def collect_all_paths_to_leaves(bp):
    """Unfold DAG to tree: every path from root to a leaf, each
    path as a list of (var, value) pairs."""
    nodes = bp["nodes"]
    paths = []

    def dfs(node_key, path):
        info = nodes.get(node_key)
        if info is None:
            return
        if "leaf" in info or "stuck" in info:
            paths.append(list(path))
            return
        var = info["var"]
        for val in (False, True):
            child_key = info["children"][val]
            lit = -var if val else var
            path.append(lit)
            dfs(child_key, path)
            path.pop()

    dfs(bp["root_state"], [])
    return paths


def emit_drat(n, k, out_path, cnf_path):
    cnf, strip_clauses, forced_e, delta = build_strip_all(n, k)
    _, _, _, branch_order, bp = build_bp(n, k)

    all_paths = collect_all_paths_to_leaves(bp)
    cuts = [frozenset(p) for p in all_paths]

    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, "w") as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(" ".join(str(l) for l in cl) + " 0\n")

    emitted = set()
    with open(out_path, "w") as f:
        # Deduplicate but keep track of multiplicities for resolution.
        unique_cuts = set(cuts)
        for cut in unique_cuts:
            if not cut:
                continue
            sorted_lits = sorted(cut, key=lambda x: (abs(x), x))
            f.write(" ".join(str(l) for l in sorted_lits) + " 0\n")
            emitted.add(cut)

        # Resolve via binary tree on branch_order vars.
        # Keep multiplicities (cuts as list, not set) so that
        # imbalanced BP paths still resolve in pairs.
        current = list(cuts)
        for v in branch_order:
            next_list = []
            pos = defaultdict(list)
            neg = defaultdict(list)
            unchanged = []
            for cls in current:
                if v in cls:
                    pos[frozenset(cls - {v})].append(cls)
                elif -v in cls:
                    neg[frozenset(cls - {-v})].append(cls)
                else:
                    unchanged.append(cls)
            # Pair up
            for rest, pos_cls_list in pos.items():
                if rest in neg:
                    if rest not in emitted:
                        sorted_lits = sorted(rest, key=lambda x: (abs(x), x))
                        if sorted_lits:
                            f.write(" ".join(str(l) for l in sorted_lits) + " 0\n")
                        emitted.add(rest)
                    next_list.append(rest)
                else:
                    # No neg counterpart; keep pos clauses
                    for c in pos_cls_list:
                        next_list.append(c)
            for rest, neg_cls_list in neg.items():
                if rest not in pos:
                    for c in neg_cls_list:
                        next_list.append(c)
            next_list.extend(unchanged)
            # Dedupe for efficiency
            current = list(set(next_list))

        if frozenset() not in emitted:
            f.write("0\n")

    return len(all_paths), len(unique_cuts), len(branch_order), len(bp["nodes"])


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_drat_v8.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf_path = f"/tmp/strip_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_n{n}_k{k}.drat"

    n_paths, n_cuts, bo_size, bp_nodes = emit_drat(n, k, drat_path, cnf_path)

    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n}, k={k}: BP nodes={bp_nodes}, |bo|={bo_size}, "
          f"paths={n_paths}, unique cuts={n_cuts}, "
          f"CNF {cnf_bytes}B, DRAT {drat_bytes}B ({drat_lines} lemmas)")

    import subprocess
    result = subprocess.run(
        ["/tmp/drat-trim", cnf_path, drat_path],
        capture_output=True, text=True, timeout=120,
    )
    for line in result.stdout.split("\n"):
        if line.startswith("s "):
            print(f"  {line}")


if __name__ == "__main__":
    main()
