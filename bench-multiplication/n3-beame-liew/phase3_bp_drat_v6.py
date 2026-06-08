#!/usr/bin/env python3
"""
N3 Phase 3 step 2 v6: use BP leaves (with merging) as cut clauses.

Key difference from v5:
  - v5 enumerates ALL 2^|bo| branch_order assignments.
  - v6 uses the BP DAG's LEAVES: each leaf represents many
    (merged) paths collapsed into a single UP-saturated state.

For each BP leaf, the cut clause is the negation of the
branching variables set along the path, augmented with any
UP-derived values needed to make the cut RUP-valid.

Strategy:
  For each BP leaf, walk back to root recording (var, value)
  pairs. The cut clause is "at least one of these was opposite".
  Since the BP reaches this leaf only when all path branches
  are set, and UP then derives a conflict, the cut is RUP-valid
  when the path branches imply a conflict purely via UP on
  strip_clauses.

  For leaves where pure UP on path branches doesn't reach
  conflict (i.e., UP needs intermediate values), we'd need to
  include UP-derived values. But in our BP construction, the
  BP's propagate function used UP-saturation AT EACH BRANCH,
  so the leaf's "conflict" was found with just the path +
  previous UP values. For drat-trim's UP to reproduce this,
  the path variables + CNF must be enough.

Let's just try: emit path-branch-only cuts and see if drat-trim
validates.
"""

import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper_order import (
    build_bp, build_strip_all, propagate,
)
from phase3_strip_extract import strip_delta


def collect_bp_paths(bp):
    """DFS through BP; return list of (path_as_literals, leaf_violated_clause)."""
    nodes = bp["nodes"]
    paths = []

    def dfs(node_key, path):
        info = nodes[node_key]
        if "leaf" in info:
            paths.append((list(path), info["leaf"]))
            return
        if "stuck" in info:
            return
        var = info["var"]
        # If both children are the same node, the branching is
        # trivial: we don't need to record this variable in the path.
        c0 = info["children"][False]
        c1 = info["children"][True]
        if c0 == c1:
            dfs(c0, path)
            return
        for val in (False, True):
            child_key = info["children"][val]
            # Cut literal is the NEGATION of branch assignment.
            lit = -var if val else var
            path.append(lit)
            dfs(child_key, path)
            path.pop()

    dfs(bp["root_state"], [])
    return paths


def emit_drat(n, k, out_path, cnf_path):
    cnf, strip_clauses, forced_e, delta = build_strip_all(n, k)
    _, _, _, branch_order, bp = build_bp(n, k)

    paths = collect_bp_paths(bp)
    cuts = set()
    for path_lits, violated in paths:
        cut = frozenset(path_lits)
        cuts.add(cut)

    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, "w") as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(" ".join(str(l) for l in cl) + " 0\n")

    emitted = set()
    with open(out_path, "w") as f:
        for cut in cuts:
            if not cut:
                continue
            sorted_lits = sorted(cut, key=lambda x: (abs(x), x))
            f.write(" ".join(str(l) for l in sorted_lits) + " 0\n")
            emitted.add(cut)

        # Resolve over branch_order vars.
        current = set(cuts)
        for v in branch_order:
            next_set = set()
            pos = {}
            neg = {}
            for cls in current:
                if v in cls:
                    pos[frozenset(cls - {v})] = cls
                elif -v in cls:
                    neg[frozenset(cls - {-v})] = cls
                else:
                    next_set.add(cls)
            for rest, pos_cls in pos.items():
                if rest in neg:
                    if rest not in emitted:
                        sorted_lits = sorted(rest, key=lambda x: (abs(x), x))
                        if sorted_lits:
                            f.write(" ".join(str(l) for l in sorted_lits) + " 0\n")
                        emitted.add(rest)
                    next_set.add(rest)
                else:
                    next_set.add(pos_cls)
            for rest, neg_cls in neg.items():
                if rest not in pos:
                    next_set.add(neg_cls)
            current = next_set

        if frozenset() not in emitted:
            f.write("0\n")

    return len(cuts), len(branch_order), len(bp["nodes"])


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_drat_v6.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf_path = f"/tmp/strip_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_n{n}_k{k}.drat"

    n_cuts, bo_size, bp_nodes = emit_drat(n, k, drat_path, cnf_path)

    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n}, k={k}: |bo|={bo_size}, BP nodes={bp_nodes}, "
          f"{n_cuts} unique cuts, CNF {cnf_bytes}B, DRAT {drat_bytes}B "
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
