#!/usr/bin/env python3
"""
N3 Phase 3 Cut(j)-merged BP DRAT emission (v2 -> v9 style).

Build BP with phase3_bp_cut_v2 row-merging, emit DRAT via
tree-unfolded post-order resolution (as in phase3_bp_drat_v9).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper_order import build_strip_all
from phase3_bp_cut_v2 import build_bp_cut_rows


def emit_tree_post_order_cut(bp, out):
    """Recursive tree-unfolded post-order emission on cut_v2 BP.

    Each BP node's clause:
      - Leaf: cut = negation of path branches.
      - Internal: resolvent of children on the branching var.
    """
    nodes = bp["nodes"]
    emitted = set()

    def rec(node_key, path):
        info = nodes.get(node_key)
        if info is None:
            return None
        if "leaf" in info or "stuck" in info:
            cl = frozenset(path)
            if cl and cl not in emitted:
                sorted_lits = sorted(cl, key=lambda x: (abs(x), x))
                out.write(" ".join(str(l) for l in sorted_lits) + " 0\n")
                emitted.add(cl)
            return cl
        var = info["var"]
        # Left (x=False): path adds +var
        path.append(var)
        c0_cl = rec(info["children"][False], path)
        path.pop()
        # Right (x=True): path adds -var
        path.append(-var)
        c1_cl = rec(info["children"][True], path)
        path.pop()

        if c0_cl is None or c1_cl is None:
            return None
        if var in c0_cl and -var in c1_cl:
            res = frozenset((c0_cl - {var}) | (c1_cl - {-var}))
        elif -var in c0_cl and var in c1_cl:
            res = frozenset((c0_cl - {-var}) | (c1_cl - {var}))
        else:
            if var not in c0_cl and -var not in c0_cl:
                res = c0_cl
            elif var not in c1_cl and -var not in c1_cl:
                res = c1_cl
            else:
                res = c0_cl & c1_cl
        if res != c0_cl and res != c1_cl and res not in emitted:
            if res:
                sorted_lits = sorted(res, key=lambda x: (abs(x), x))
                out.write(" ".join(str(l) for l in sorted_lits) + " 0\n")
                emitted.add(res)
            elif not res and frozenset() not in emitted:
                out.write("0\n")
                emitted.add(frozenset())
        return res

    root_cl = rec(bp["root"], [])
    if root_cl is not None and not root_cl and frozenset() not in emitted:
        out.write("0\n")
        emitted.add(frozenset())
    return emitted


def emit_drat_cut(n, k, out_path, cnf_path):
    cnf, strip_clauses, forced_e, delta = build_strip_all(n, k)
    bp = build_bp_cut_rows(n, k)

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
        print("usage: phase3_bp_cut_drat.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf_path = f"/tmp/strip_cut_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_cut_n{n}_k{k}.drat"
    emit_drat_cut(n, k, drat_path, cnf_path)

    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n}, k={k}: CNF {cnf_bytes}B, DRAT {drat_bytes}B "
          f"({drat_lines} lemmas)")

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
