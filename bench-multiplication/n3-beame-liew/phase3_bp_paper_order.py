#!/usr/bin/env python3
"""
N3 Phase 3 step 2: Beame-Liew BP with paper's variable ordering.

Variable-branching order (per Lemma 3.2, Corollary 3.3):
  1. Output bits c[i] (= acc_c[last_row, i]) and d[i] for
     i in [k-Delta, k].
  2. Incoming carries at column k-Delta-1, both multipliers:
     cry_c[j, k-Delta-1] and cry_d[j, k-Delta-1] for j in [1, n-1].
  3. Tableau variables pp_c[i, j] for i+j in [k-Delta, k], ordered
     by j increasing (which matches "row-by-row" in B-L).

Merging:
  Two BP nodes merge if, after UP-saturation of the branches taken
  so far, they have identical remaining "live" assignments.
  Concretely: sort the UP-derived assignments and use as a hashable
  key.

Leaves:
  UP-saturation derives a conflict; the leaf's clause is the
  violated strip clause (for DRAT emission we'll use that clause
  as the RUP-derivable witness).

Usage: python3 phase3_bp_paper_order.py N K
"""

import math
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from generate_array_mul_comm_meta import build_commutativity_cnf_meta
from phase3_strip_extract import (
    extract_strip,
    strip_delta,
)


def propagate(clauses, assign):
    """UP; returns (final, conflict)."""
    assign = dict(assign)
    changed = True
    while changed:
        changed = False
        for cl in clauses:
            unassigned = []
            satisfied = False
            for lit in cl:
                v = abs(lit)
                if v in assign:
                    val = assign[v] if lit > 0 else not assign[v]
                    if val:
                        satisfied = True
                        break
                else:
                    unassigned.append(lit)
            if satisfied:
                continue
            if len(unassigned) == 0:
                return assign, cl
            if len(unassigned) == 1:
                lit = unassigned[0]
                v = abs(lit)
                new_val = lit > 0
                if v in assign and assign[v] != new_val:
                    return assign, cl
                assign[v] = new_val
                changed = True
    return assign, None


def build_strip_all(n, k):
    cnf, _, _, _, _ = build_commutativity_cnf_meta(n)
    delta = strip_delta(n)
    strip_clauses = list(extract_strip(cnf, k, delta))
    forced_e = {}
    for v, role in cnf.meta.items():
        if role and role[0] == "diff":
            bit = role[1]
            if bit < k:
                strip_clauses.append([-v])
                forced_e[v] = False
            elif bit == k:
                strip_clauses.append([v])
                forced_e[v] = True
    return cnf, strip_clauses, forced_e, delta


def get_output_var(cnf, side, col):
    """Return the CNF variable representing c[col] or d[col]."""
    best = None
    best_row = -1
    for v, role in cnf.meta.items():
        if role and role[0] == f"acc_{side}" and role[2] == col:
            if role[1] > best_row:
                best = v
                best_row = role[1]
    if best is None:
        for v, role in cnf.meta.items():
            if role and role[0] == f"pp_{side}" and role[1] == 0 and role[2] == col:
                return v
    return best


def branching_vars_in_order(cnf, k, delta, n):
    """Return the ordered list of variables to branch on, per B-L.

    Order: outputs c[k-Delta..k] then d[k-Delta..k], then incoming
    carries at col k-Delta-1 both sides for each row, then tableau
    pp_c[i, j] with i+j in [k-Delta, k] by increasing j.
    """
    strip_cols = list(range(max(0, k - delta), k + 1))
    vars_order = []

    # (1) Outputs.
    for col in strip_cols:
        c_v = get_output_var(cnf, "c", col)
        if c_v is not None:
            vars_order.append(c_v)
    for col in strip_cols:
        d_v = get_output_var(cnf, "d", col)
        if d_v is not None:
            vars_order.append(d_v)

    # (2) Incoming carries at col k-Delta-1.
    carry_col = max(0, k - delta - 1)
    if carry_col >= 0 and carry_col < k - delta + 1:
        # Only relevant if there are carries crossing the boundary.
        for side in ("c", "d"):
            for row in range(1, n):
                for v, role in cnf.meta.items():
                    if (role and role[0] == f"cry_{side}" and
                            role[1] == row and role[2] == carry_col):
                        if v not in vars_order:
                            vars_order.append(v)

    # (3) Tableau, by j (column of pp = i+j) increasing.
    tableau_by_col = defaultdict(list)
    for v, role in cnf.meta.items():
        if role and role[0] == "pp_c":
            i, j = role[1], role[2]
            col = i + j
            if k - delta <= col <= k:
                tableau_by_col[col].append(v)
    for col in sorted(tableau_by_col):
        for v in sorted(tableau_by_col[col]):
            if v not in vars_order:
                vars_order.append(v)

    return vars_order


def build_bp(n, k, verbose=False):
    """Build the BP for phi_Strip(k). Returns BP DAG."""
    cnf, strip_clauses, forced_e, delta = build_strip_all(n, k)
    branch_order = branching_vars_in_order(cnf, k, delta, n)

    if verbose:
        print(f"n={n}, k={k}, Delta={delta}")
        print(f"Branching variables in order ({len(branch_order)} total):")
        for v in branch_order:
            role = cnf.meta.get(v)
            print(f"  v{v}: {role}")

    # BP construction via BFS.
    # Each node: (state_key, branching_var) -> {0: child_node, 1: child_node, leaf_clause}.
    # state_key = frozenset of (var, value) for UP-derived assignments minus forced_e.

    def state_key(assign):
        # Exclude forced_e from the key (they're constants).
        return frozenset(
            (v, val) for v, val in assign.items()
            if v not in forced_e
        )

    # Compute initial UP.
    init_final, init_conflict = propagate(strip_clauses, forced_e)
    if init_conflict is not None:
        # Strip refutes immediately by UP. Trivial BP.
        return cnf, strip_clauses, forced_e, branch_order, {
            "root_state": state_key(init_final),
            "nodes": {state_key(init_final): {"leaf": init_conflict}},
            "branch_order": branch_order,
        }

    # Build BP level-by-level. At each level L, pick branch_order[L]
    # and split each existing leaf into two children.
    # We represent nodes by state key; two states merge into one.

    # nodes[key] = dict with either {"level": L, "var": branch_var, "children": {0: key0, 1: key1}}
    #             or {"leaf": violated_clause}
    nodes = {}
    root_key = state_key(init_final)
    frontier = [(init_final, root_key, 0)]  # (assign, key, level)
    nodes[root_key] = None  # placeholder

    while frontier:
        assign, key, level = frontier.pop()
        if nodes.get(key) is not None and "var" in nodes[key]:
            # Already expanded.
            continue
        # Advance past any branching vars already assigned.
        while level < len(branch_order) and branch_order[level] in assign:
            level += 1
        if level >= len(branch_order):
            # Ran out of branching vars. If no conflict, this is a
            # "stuck" node -- should not happen for UNSAT strips but
            # we'll emit a failure diagnostic.
            nodes[key] = {"stuck": True}
            continue
        var = branch_order[level]
        children = {}
        for bit in (False, True):
            new_assign = dict(assign)
            new_assign[var] = bit
            new_final, conflict = propagate(strip_clauses, new_assign)
            if conflict is not None:
                # Leaf.
                leaf_key = ("leaf", tuple(conflict))
                nodes[leaf_key] = {"leaf": list(conflict)}
                children[bit] = leaf_key
            else:
                child_key = state_key(new_final)
                if child_key not in nodes:
                    nodes[child_key] = None
                    frontier.append((new_final, child_key, level + 1))
                children[bit] = child_key
        nodes[key] = {"level": level, "var": var, "children": children}

    return cnf, strip_clauses, forced_e, branch_order, {
        "root_state": root_key,
        "nodes": nodes,
        "branch_order": branch_order,
    }


def main():
    if len(sys.argv) < 3:
        print("usage: phase3_bp_paper_order.py N K [--verbose]", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])
    verbose = "--verbose" in sys.argv

    cnf, strip_clauses, forced_e, branch_order, bp = build_bp(n, k, verbose=verbose)

    # Count nodes by type.
    total = len(bp["nodes"])
    leaves = sum(1 for info in bp["nodes"].values()
                 if info and "leaf" in info)
    internal = sum(1 for info in bp["nodes"].values()
                   if info and "var" in info)
    stuck = sum(1 for info in bp["nodes"].values()
                if info and "stuck" in info)
    print(f"n={n}, k={k}: BP has {total} nodes ({internal} internal, "
          f"{leaves} leaves, {stuck} stuck)")
    if stuck:
        print("WARNING: BP has stuck nodes (ran out of branching vars "
              "without reaching conflict). The branching order may need "
              "to include more variables.")


if __name__ == "__main__":
    main()
