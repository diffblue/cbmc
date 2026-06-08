#!/usr/bin/env python3
"""
N3 Phase 3 step 2 BP DRAT emission (v2).

Strategy: for each BP node v (including internal and leaves), the
"path clause" at v is the disjunction of NEGATIONS of the branch
assignments from root to v. So:
  - Root has the empty path clause (equivalent to the goal: unsat).
  - Going down the BP, path clauses grow by one literal per level.
  - At a leaf, the path clause says "NOT this branch". Since the
    leaf is reached only when UP derives a conflict, the path
    clause is RUP-derivable (assume path, UP gives conflict).

DRAT emission: post-order traversal. At each node, emit the path
clause. Merging (two paths reach same node) is sound because the
PATH CLAUSE at the merged node is the RESOLVENT of the two
incoming paths on the branching variable.

To keep DRAT valid:
  - At each node, emit the path clause (disjunction of neg-branch-
    literals).
  - At internal nodes, the path clause follows by resolution from
    its children's path clauses on the branching variable.
  - At leaves, the path clause follows from the violated CNF clause
    by weakening (which is also RUP-valid if the leaf's CNF clause
    plus UP derive the path-clause literals).

Actually simpler: each emitted clause needs to be RUP-valid in the
accumulating set. The key insight is that assuming NOT(path-clause)
forces the branch assignment, UP then reaches a conflict with the
CNF (because the strip is UNSAT under any full assignment).

If we emit path clauses from ROOT (empty) to LEAVES (long), the
empty clause at the root is what we emit LAST. But we emit them
post-order from leaves to root, shortening as we go.

For merging: if two paths A and B converge to node v, the path
clause at v is the resolvent of the paths on the common/differing
variables -- specifically, it equals the one shorter clause that
covers both.

Implementation: for each (a, b) input in the BP enumeration, find
the path taken (sequence of (var, value) pairs). For each leaf,
the path clause = negation of the assignments.

For DRAT: emit cut clauses in DECREASING path length, progressively
resolving. This is Phase 1 style within the BP. 

Let's try this.
"""

import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper_order import (
    build_bp, build_strip_all, propagate,
)
from phase3_strip_extract import strip_delta


def enumerate_paths(bp):
    """Walk through the BP starting from root, emitting all paths
    to leaves. Each path is a list of (var, value) pairs PLUS the
    leaf's full UP-saturated assignment."""
    root_key = bp["root_state"]
    nodes = bp["nodes"]

    paths = []  # each path: (branch_list, leaf_assign, violated_clause)

    def dfs(node_key, path):
        info = nodes[node_key]
        if "leaf" in info:
            paths.append((list(path), info.get("leaf_assign"), info["leaf"]))
            return
        if "stuck" in info:
            paths.append((list(path), None, None))
            return
        var = info["var"]
        for val in (False, True):
            child_key = info["children"][val]
            path.append((var, val))
            dfs(child_key, path)
            path.pop()

    dfs(root_key, [])
    return paths


def path_to_cut_clause(path):
    """Convert a path = list of (var, value) pairs to a cut clause:
    the disjunction of literals NEGATING each branch assignment."""
    lits = []
    for var, val in path:
        # If branch assigned var = val (True/False), negation is -var
        # (when val=True) or var (when val=False).
        lits.append(-var if val else var)
    return frozenset(lits)


def emit_drat_via_paths(n, k, out_path):
    """Emit DRAT for phi_Strip(k) using Phase 1 style cut clauses
    but restricted to the BP's paths. The BP's merging naturally
    reduces the number of distinct paths compared to flat
    enumeration."""
    cnf, strip_clauses, forced_e, branch_order, bp = build_bp(n, k)

    paths = enumerate_paths(bp)

    # Each path's cut clause.
    cut_clauses = []
    for path, violated in paths:
        if violated is None:
            continue  # stuck (shouldn't happen for UNSAT strips)
        cc = path_to_cut_clause(path)
        cut_clauses.append(cc)

    # Deduplicate cut clauses.
    unique_cuts = set(cut_clauses)

    # Emit all cut clauses, then resolve.
    vars_in_branch_order = list(branch_order)

    with open(out_path, "w") as f:
        emitted = set()
        for cc in unique_cuts:
            if not cc:  # empty cut clause -- handle below
                continue
            sorted_lits = sorted(cc, key=lambda x: (abs(x), x))
            f.write(" ".join(str(x) for x in sorted_lits) + " 0\n")
            emitted.add(cc)

        # Binary-resolution tree over branch-order variables (same as
        # Phase 1 v2).
        current = set(unique_cuts)
        for v in vars_in_branch_order:
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
                    resolvent = sorted(rest, key=lambda x: (abs(x), x))
                    if rest in emitted:
                        next_set.add(rest)
                        continue
                    if resolvent:
                        f.write(" ".join(str(x) for x in resolvent) + " 0\n")
                    else:
                        f.write("0\n")
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
        print("usage: phase3_bp_drat_v2.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf_path = f"/tmp/strip_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_n{n}_k{k}.drat"
    write_strip_cnf(n, k, cnf_path)
    emit_drat_via_paths(n, k, drat_path)

    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n}, k={k}: CNF {cnf_bytes}B, DRAT {drat_bytes}B "
          f"({drat_lines} lemmas)")

    # Validate.
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
