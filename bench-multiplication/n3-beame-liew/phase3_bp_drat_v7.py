#!/usr/bin/env python3
"""
N3 Phase 3 step 2 v7: proper DAG-based cut emission.

For each BP node, collect ALL paths from root to that node.
The node's clause is the INTERSECTION of all paths' negations
(smallest set of literals that must be falsified on every path
to reach the node).

For internal BP nodes whose branching var x has two children
c0 (x=False) and c1 (x=True):
  clause(c0) must contain +x (path adds x=F).
  clause(c1) must contain -x.
  clause(internal_node) = resolve(clause(c0), clause(c1), x).

Post-order emit: each internal node's clause appears after
children's.

This is Prop 2.1 from Beame-Liew, adapted to DAG BPs.
"""

import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper_order import (
    build_bp, build_strip_all, propagate,
)


def collect_all_paths_per_node(bp):
    """For each BP node, collect the set of path-literal-sets
    (each path = list of literals negating the branches taken)."""
    nodes = bp["nodes"]
    # paths_at[node_key] = set of frozensets, each representing
    # one path from root to node_key.
    paths_at = defaultdict(set)

    def dfs(node_key, path):
        paths_at[node_key].add(frozenset(path))
        info = nodes.get(node_key)
        if info is None or "leaf" in info or "stuck" in info:
            return
        var = info["var"]
        for val in (False, True):
            lit = -var if val else var
            child_key = info["children"][val]
            path.append(lit)
            dfs(child_key, path)
            path.pop()

    dfs(bp["root_state"], [])
    return paths_at


def intersection_clause(path_set):
    """Return intersection of all paths (as literal set).
    
    If only one path, return that path. If multiple, return the
    literals common to all.
    """
    if not path_set:
        return frozenset()
    paths_list = list(path_set)
    common = set(paths_list[0])
    for p in paths_list[1:]:
        common &= set(p)
    return frozenset(common)


def postorder(bp):
    """Return nodes in post-order (children before parents)."""
    nodes = bp["nodes"]
    visited = set()
    order = []

    def visit(node_key):
        if node_key in visited:
            return
        visited.add(node_key)
        info = nodes.get(node_key)
        if info and "var" in info:
            for child in info["children"].values():
                visit(child)
        order.append(node_key)

    visit(bp["root_state"])
    return order


def emit_drat(n, k, out_path, cnf_path):
    cnf, strip_clauses, forced_e, delta = build_strip_all(n, k)
    _, _, _, branch_order, bp = build_bp(n, k)

    paths_at = collect_all_paths_per_node(bp)
    node_order = postorder(bp)
    nodes = bp["nodes"]

    # Compute clause per node as intersection of all paths.
    node_clauses = {}
    for nk in node_order:
        node_clauses[nk] = intersection_clause(paths_at[nk])

    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, "w") as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(" ".join(str(l) for l in cl) + " 0\n")

    emitted = set()
    with open(out_path, "w") as f:
        for nk in node_order:
            cl = node_clauses[nk]
            if not cl:
                if nk == bp["root_state"]:
                    # Empty clause at root.
                    f.write("0\n")
                    emitted.add(cl)
                continue
            if cl in emitted:
                continue
            sorted_lits = sorted(cl, key=lambda x: (abs(x), x))
            f.write(" ".join(str(l) for l in sorted_lits) + " 0\n")
            emitted.add(cl)

        # If root's clause isn't empty, we need to derive empty
        # separately -- resolve on branch_order.
        root_cl = node_clauses[bp["root_state"]]
        if root_cl and frozenset() not in emitted:
            # Shouldn't happen if BP is well-formed.
            print(f"WARN: root clause non-empty: {root_cl}", file=sys.stderr)
            f.write("0\n")

    return len(node_order), len(branch_order), len(bp["nodes"])


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_drat_v7.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf_path = f"/tmp/strip_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_n{n}_k{k}.drat"

    n_nodes, bo_size, bp_nodes = emit_drat(n, k, drat_path, cnf_path)

    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n}, k={k}: BP nodes={bp_nodes}, |bo|={bo_size}, "
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
