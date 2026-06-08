#!/usr/bin/env python3
"""
N3 Phase 3 step 2 v9: unfold BP DAG to a tree, emit resolvents
in post-order.

For each path from root to a leaf (tree-style), and each tree
node's clause = path from root to that node. Leaves have full
path clause; internal nodes emit the resolvent of their children
on the branching variable.

The resolvent construction:
  - At leaf: cut = negation of path literals.
  - At internal with branching x, left child (x=F), right child (x=T):
    Their cuts contain +x and -x respectively (from the branch).
    Resolve on x to get the parent's cut (shorter by 1 literal).

Emit EACH INTERNAL NODE's CUT as a lemma, in post-order. Each is
RUP-valid because it's a resolvent of previously emitted cuts.

Final root's cut should be empty.
"""

import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper_order import (
    build_bp, build_strip_all, propagate,
)


def emit_tree_post_order(bp, strip_clauses, out):
    """Unfold BP to tree, emit post-order resolvents."""
    nodes = bp["nodes"]
    emitted = set()

    def rec(node_key, path):
        """Returns the clause (frozenset of literals) at this node."""
        info = nodes.get(node_key)
        if info is None:
            return None
        if "leaf" in info or "stuck" in info:
            # Clause = negation of path.
            cl = frozenset(path)
            if cl and cl not in emitted:
                sorted_lits = sorted(cl, key=lambda x: (abs(x), x))
                out.write(" ".join(str(l) for l in sorted_lits) + " 0\n")
                emitted.add(cl)
            return cl
        var = info["var"]
        # Left (x=False) branch: path adds +var literal.
        path.append(var)  # literal +var
        c0_cl = rec(info["children"][False], path)
        path.pop()
        # Right (x=True) branch: path adds -var literal.
        path.append(-var)
        c1_cl = rec(info["children"][True], path)
        path.pop()

        # Resolve on var.
        if c0_cl is None or c1_cl is None:
            return None
        if var in c0_cl and -var in c1_cl:
            res = frozenset((c0_cl - {var}) | (c1_cl - {-var}))
        elif -var in c0_cl and var in c1_cl:
            # Unusual: c0 has -var? Shouldn't happen if paths are as
            # expected, but handle.
            res = frozenset((c0_cl - {-var}) | (c1_cl - {var}))
        else:
            # Neither child has the branching var as expected.
            # One of them might not contain var (e.g., leaf with a
            # merged cut that doesn't include var). In that case,
            # the child's clause is "stronger" and doesn't need
            # resolution -- just use it.
            if var not in c0_cl and -var not in c0_cl:
                res = c0_cl
            elif var not in c1_cl and -var not in c1_cl:
                res = c1_cl
            else:
                # Both have var with same polarity? Then resolution
                # doesn't apply; use intersection.
                res = c0_cl & c1_cl
        if res != c0_cl and res != c1_cl and res not in emitted:
            # New resolvent; emit.
            if res:
                sorted_lits = sorted(res, key=lambda x: (abs(x), x))
                out.write(" ".join(str(l) for l in sorted_lits) + " 0\n")
                emitted.add(res)
            elif not res and frozenset() not in emitted:
                out.write("0\n")
                emitted.add(frozenset())
        return res

    root_cl = rec(bp["root_state"], [])
    if root_cl is not None and not root_cl and frozenset() not in emitted:
        out.write("0\n")
        emitted.add(frozenset())
    return emitted


def emit_drat(n, k, out_path, cnf_path):
    cnf, strip_clauses, forced_e, delta = build_strip_all(n, k)
    _, _, _, branch_order, bp = build_bp(n, k)

    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, "w") as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(" ".join(str(l) for l in cl) + " 0\n")

    with open(out_path, "w") as f:
        emit_tree_post_order(bp, strip_clauses, f)

    return len(branch_order), len(bp["nodes"])


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_drat_v9.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf_path = f"/tmp/strip_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_n{n}_k{k}.drat"

    bo_size, bp_nodes = emit_drat(n, k, drat_path, cnf_path)

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
