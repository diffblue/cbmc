#!/usr/bin/env python3
"""
N3 Phase 3 step 2: emit DRAT from the paper-order BP.

Strategy:
  - Build the BP via phase3_bp_paper_order.build_bp.
  - For each node, compute a "clause" via Prop 2.1: leaf = violated
    CNF clause; internal v (branching x, children v0, v1) = resolvent
    of clause(v0) and clause(v1) on x.
  - Post-order traversal: emit each non-trivial resolvent as a RUP
    lemma. If resolving two children gives a clause identical to
    one of them, we skip (no new lemma needed).
  - Final root clause should be empty; emit the empty clause.

Validate with drat-trim.
"""

import math
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper_order import build_bp, build_strip_all
from phase3_strip_extract import extract_strip, strip_delta
from generate_array_mul_comm_meta import build_commutativity_cnf_meta


def resolve(clause_a, clause_b, var):
    """Resolve clause_a and clause_b on variable var. Returns a frozenset
    of literals, or None if resolution is not possible (neither
    clause contains var or both contain the same polarity)."""
    a_has_pos = var in clause_a
    a_has_neg = -var in clause_a
    b_has_pos = var in clause_b
    b_has_neg = -var in clause_b
    if a_has_pos and b_has_neg:
        return frozenset((clause_a - {var}) | (clause_b - {-var}))
    if a_has_neg and b_has_pos:
        return frozenset((clause_a - {-var}) | (clause_b - {var}))
    # No complementary literals.
    return None


def compute_node_clauses(bp, cnf, forced_e):
    """Compute the clause at each BP node via post-order traversal.

    Returns dict node_key -> frozenset of literals.

    For leaves: clause = violated CNF clause (as frozenset).
    For internal v with branching var x and children v0, v1:
      clause(v) = resolve(clause(v0), clause(v1), x), or if
      resolution isn't applicable, clause(v) = clause(v0) intersect
      clause(v1) (weakening).
    """
    nodes = bp["nodes"]

    # Topological sort: leaves first, then internal in reverse order
    # of creation. Since we did BFS building, later-in-frontier nodes
    # depend on earlier leaves. Let's do DFS post-order.
    node_clauses = {}
    post_order = []
    visited = set()

    def visit(node_key):
        if node_key in visited:
            return
        visited.add(node_key)
        info = nodes.get(node_key)
        if info is None:
            return
        if "leaf" in info:
            post_order.append(node_key)
            return
        if "stuck" in info:
            post_order.append(node_key)
            return
        # Internal.
        for child_key in info["children"].values():
            visit(child_key)
        post_order.append(node_key)

    visit(bp["root_state"])

    for node_key in post_order:
        info = nodes[node_key]
        if "leaf" in info:
            node_clauses[node_key] = frozenset(info["leaf"])
        elif "stuck" in info:
            node_clauses[node_key] = None  # can't resolve
        else:
            var = info["var"]
            c0 = node_clauses[info["children"][False]]
            c1 = node_clauses[info["children"][True]]
            if c0 is None or c1 is None:
                node_clauses[node_key] = None
                continue
            r = resolve(c0, c1, var)
            if r is None:
                # Neither child mentions var (or both same polarity).
                # Weaken to the intersection of both.
                r = c0 & c1
            node_clauses[node_key] = r
    return node_clauses, post_order


def emit_drat(n, k, cnf, strip_clauses, forced_e, bp, out_path):
    """Emit DRAT for the BP refutation of phi_Strip(k)."""
    node_clauses, post_order = compute_node_clauses(bp, cnf, forced_e)

    emitted = set()
    # Add original CNF clauses to emitted (they don't need re-emitting).
    for cl in strip_clauses:
        emitted.add(frozenset(cl))

    lines = 0
    with open(out_path, "w") as f:
        for node_key in post_order:
            info = bp["nodes"][node_key]
            if "leaf" in info:
                # Leaf's clause is already in CNF; nothing to emit.
                continue
            if "stuck" in info:
                continue
            cl = node_clauses[node_key]
            if cl is None:
                continue
            if cl in emitted:
                continue
            emitted.add(cl)
            # Emit as DRAT lemma.
            sorted_lits = sorted(cl, key=lambda x: (abs(x), x))
            f.write(" ".join(str(lit) for lit in sorted_lits) + " 0\n")
            lines += 1
        # Finally emit empty clause if the root clause is empty.
        root_cl = node_clauses.get(bp["root_state"])
        if root_cl is not None and len(root_cl) == 0:
            if frozenset() not in emitted:
                f.write("0\n")
                lines += 1
        else:
            # Root clause non-empty means BP doesn't fully refute.
            # Print diagnostic.
            print(f"WARN: root clause is {root_cl}, expected empty",
                  file=sys.stderr)
    return lines


def write_strip_cnf(n, k, out_path):
    cnf, strip_clauses, forced_e, delta = build_strip_all(n, k)
    used_vars = set()
    for cl in strip_clauses:
        for lit in cl:
            used_vars.add(abs(lit))
    max_var = max(used_vars) if used_vars else 1
    with open(out_path, "w") as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(" ".join(str(lit) for lit in cl) + " 0\n")


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_drat.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf, strip_clauses, forced_e, branch_order, bp = build_bp(n, k)

    cnf_path = f"/tmp/strip_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_n{n}_k{k}.drat"
    write_strip_cnf(n, k, cnf_path)

    drat_lines = emit_drat(n, k, cnf, strip_clauses, forced_e, bp, drat_path)

    # Measure.
    drat_bytes = os.path.getsize(drat_path)
    cnf_bytes = os.path.getsize(cnf_path)
    bp_nodes = len(bp["nodes"])
    print(f"n={n}, k={k}: CNF {cnf_bytes}B, DRAT {drat_bytes}B "
          f"({drat_lines} lemmas), BP {bp_nodes} nodes")

    # Validate with drat-trim.
    import subprocess
    result = subprocess.run(
        ["/tmp/drat-trim", cnf_path, drat_path],
        capture_output=True, text=True, timeout=60,
    )
    for line in result.stdout.split("\n"):
        if line.startswith("s "):
            print(f"  {line}")


if __name__ == "__main__":
    main()
