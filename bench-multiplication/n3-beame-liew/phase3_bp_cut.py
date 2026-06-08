#!/usr/bin/env python3
"""
N3 Phase 3 step 2 polynomial attempt: BP with Cut(j) state merging.

Paper's Cut(j) at level j (processing row j of the multiplier):
   Cut(j) = {acc_c[j, col], cry_c[j, col], acc_d[j, col], cry_d[j, col]
             : col in [k-Delta, k]}

For ripple-carry, this is the accumulator + carry state at row j
across the strip columns. At most 4*(Delta+1) = O(log k) variables
per cut. State space 2^{O(log k)} = poly(k).

The BP branches on tableau variables pp_c[i, j] in order of
increasing row j. At each row boundary, states merge by Cut(j).

Within a row, additionally branch on outputs (c[col], d[col]
for col in strip) and incoming carries.
"""

import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper_order import (
    build_strip_all, propagate,
)
from phase3_strip_extract import strip_delta
from generate_array_mul_comm_meta import build_commutativity_cnf_meta


def get_cut_vars(cnf, k, delta, n):
    """Return the set of variables that form the Cut(j) structure
    for each row j in [1, n-1]. Returns dict row -> set of vars."""
    cut_vars = defaultdict(set)
    strip_cols = list(range(max(0, k - delta), k + 1))
    for v, role in cnf.meta.items():
        if not role:
            continue
        tag = role[0]
        if tag in ("acc_c", "acc_d", "cry_c", "cry_d"):
            row, col = role[1], role[2]
            if col in strip_cols:
                cut_vars[row].add(v)
    return cut_vars


def cut_aware_branch_order(cnf, k, delta, n):
    """Branching order for Cut(j) merging.

    Order by row. Within each row j, branch on:
      1. Tableau vars pp_c[i, j] with i+j in strip range.
      2. Outputs acc_c[last_row, col] and acc_d[last_row, col]
         for col in strip (once we're in the last row).

    Returns: list of (var, row_j_for_state_merging).
    """
    strip_cols = list(range(max(0, k - delta), k + 1))
    order = []

    # Outputs (at last row)
    for col in strip_cols:
        for v, role in cnf.meta.items():
            if role and role[0] == "acc_c" and role[2] == col:
                order.append((v, n - 1))
                break
    for col in strip_cols:
        for v, role in cnf.meta.items():
            if role and role[0] == "acc_d" and role[2] == col:
                order.append((v, n - 1))
                break

    # Tableau vars by row
    for i in range(n):
        for j in range(n):
            col = i + j
            if col in strip_cols:
                for v, role in cnf.meta.items():
                    if (role and role[0] == "pp_c"
                            and role[1] == i and role[2] == j):
                        order.append((v, i))
                        break
    return order


def build_bp_cut(n, k):
    cnf, strip_clauses, forced_e, delta = build_strip_all(n, k)
    branch_order = cut_aware_branch_order(cnf, k, delta, n)
    cut_vars_by_row = get_cut_vars(cnf, k, delta, n)

    # State key: (row_so_far, frozenset of (cut_var, value) for Cut(row)).
    # As we branch through levels, row increases. When we cross a row
    # boundary, we reset state to just Cut(row).

    def state_key(assign, row_seen):
        # Take only Cut(row_seen) variables from assign.
        # If row_seen is the max row, include all cut levels up to it.
        cut_set = set()
        for r in range(row_seen + 1):
            cut_set |= cut_vars_by_row.get(r, set())
        # Only include cut vars that are in assign and not forced_e.
        return frozenset(
            (v, assign[v]) for v in cut_set
            if v in assign and v not in forced_e
        )

    # BFS.
    init_final, init_conflict = propagate(strip_clauses, forced_e)
    if init_conflict is not None:
        return {"root_state": (0, frozenset()), "nodes": {}, "branch_order": branch_order,
                "conflict_at_root": init_conflict}

    root_key = (0, state_key(init_final, 0))
    nodes = {root_key: None}
    # Each frontier entry: (assign, key, level).
    frontier = [(init_final, root_key, 0)]

    while frontier:
        assign, key, level = frontier.pop()
        if nodes.get(key) is not None and "var" in nodes[key]:
            continue
        # Advance past any branching vars already assigned.
        while level < len(branch_order) and branch_order[level][0] in assign:
            level += 1
        if level >= len(branch_order):
            nodes[key] = {"stuck": True}
            continue
        var, var_row = branch_order[level]
        children = {}
        for bit in (False, True):
            new_assign = dict(assign)
            new_assign[var] = bit
            new_final, conflict = propagate(strip_clauses, new_assign)
            if conflict is not None:
                leaf_key = ("leaf", tuple(conflict))
                nodes[leaf_key] = {"leaf": list(conflict)}
                children[bit] = leaf_key
            else:
                child_key = (var_row, state_key(new_final, var_row))
                if child_key not in nodes:
                    nodes[child_key] = None
                    frontier.append((new_final, child_key, level + 1))
                children[bit] = child_key
        nodes[key] = {"level": level, "var": var, "children": children}

    return {"root_state": root_key, "nodes": nodes, "branch_order": branch_order}


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_cut.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    bp = build_bp_cut(n, k)
    total = len(bp["nodes"])
    leaves = sum(1 for i in bp["nodes"].values() if i and "leaf" in i)
    stuck = sum(1 for i in bp["nodes"].values() if i and "stuck" in i)
    internal = sum(1 for i in bp["nodes"].values() if i and "var" in i)
    print(f"n={n}, k={k}: Cut(j)-BP nodes={total} "
          f"({internal} int, {leaves} leaves, {stuck} stuck), "
          f"|bo|={len(bp['branch_order'])}")


if __name__ == "__main__":
    main()
