#!/usr/bin/env python3
"""
N3 Phase 3: DAG-based Prop 2.1 resolution emission.

For each BP node, compute ONE clause based on its children
(resolvent on branching var, or children's clause if only one
applies). Emit each clause exactly once in post-order.

Leaves: clause = violated CNF clause (with path-specific literals
added to make it falsifiable).

Key difference from tree-unfolded v9:
- v9 visits each node potentially multiple times via DFS recursion,
  producing path-specific clauses.
- This DAG version visits each node ONCE, producing ONE clause.
- Size is proportional to BP node count (not path count).

Returns True if resolvents give empty clause at root; False otherwise.
"""

import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper_order import build_strip_all


def resolve_on(cl_a, cl_b, var):
    """Resolve cl_a, cl_b on var if possible. Return (resolvent, ok).
    If neither cl has var, return (cl_a or cl_b, True) (no resolution needed).
    If both have same polarity, return (shorter, True).
    If complementary, resolve.
    """
    a_pos = var in cl_a
    a_neg = -var in cl_a
    b_pos = var in cl_b
    b_neg = -var in cl_b

    if a_pos and b_neg:
        return frozenset((cl_a - {var}) | (cl_b - {-var}))
    if a_neg and b_pos:
        return frozenset((cl_a - {-var}) | (cl_b - {var}))
    # Not complementary. Use child whose clause doesn't mention var.
    if not (a_pos or a_neg):
        return cl_a
    if not (b_pos or b_neg):
        return cl_b
    # Both have same polarity. Take their intersection as weakest.
    return cl_a & cl_b


def dag_postorder(bp):
    """Return DAG nodes in post-order (children before parents)."""
    nodes = bp["nodes"]
    visited = set()
    order = []

    def visit(nk):
        if nk in visited:
            return
        visited.add(nk)
        info = nodes.get(nk)
        if info and "var" in info:
            for child in info["children"].values():
                visit(child)
        order.append(nk)

    root = bp.get("root") or bp.get("root_state")
    visit(root)
    return order


def emit_drat_dag(bp, strip_clauses, out):
    """Emit DRAT via DAG Prop 2.1. Returns root's clause."""
    nodes = bp["nodes"]
    order = dag_postorder(bp)
    node_clauses = {}
    emitted = set()

    # Add all strip clauses to emitted (so we don't re-emit them).
    for cl in strip_clauses:
        emitted.add(frozenset(cl))

    for nk in order:
        info = nodes.get(nk)
        if info is None:
            node_clauses[nk] = None
            continue
        if "leaf" in info:
            cl = frozenset(info["leaf"])
            node_clauses[nk] = cl
            continue
        if "stuck" in info:
            node_clauses[nk] = None
            continue
        # Internal node.
        var = info["var"]
        c0 = info["children"].get(False)
        c1 = info["children"].get(True)
        cl0 = node_clauses.get(c0)
        cl1 = node_clauses.get(c1)
        if cl0 is None or cl1 is None:
            node_clauses[nk] = None
            continue
        # Resolve on var.
        res = resolve_on(cl0, cl1, var)
        node_clauses[nk] = res
        # Emit if new.
        if res and res not in emitted:
            sorted_lits = sorted(res, key=lambda x: (abs(x), x))
            out.write(" ".join(str(l) for l in sorted_lits) + " 0\n")
            emitted.add(res)
        elif not res and frozenset() not in emitted:
            out.write("0\n")
            emitted.add(frozenset())

    root = bp.get("root") or bp.get("root_state")
    return node_clauses.get(root)


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_dag_drat.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    from phase3_bp_diag import build_bp_diag
    cnf, strip_clauses, forced_e, delta = build_strip_all(n, k)
    bp = build_bp_diag(n, k)

    cnf_path = f"/tmp/strip_dag_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_dag_n{n}_k{k}.drat"

    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, "w") as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(" ".join(str(l) for l in cl) + " 0\n")

    with open(drat_path, "w") as f:
        if bp.get("conflict") is not None:
            f.write("0\n")
            root_cl = frozenset()
        else:
            root_cl = emit_drat_dag(bp, strip_clauses, f)
        # Ensure empty clause emitted.
        if root_cl != frozenset():
            f.write("0\n")

    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n}, k={k}: CNF {cnf_bytes}B, DRAT {drat_bytes}B "
          f"({drat_lines} lemmas), root_cl={len(root_cl) if root_cl else 0}")

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
