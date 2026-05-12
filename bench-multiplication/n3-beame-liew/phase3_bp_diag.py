#!/usr/bin/env python3
"""
N3 Phase 3 step 4: BP with diagonal (column) ordering, aligning with
paper's §3.3 construction.

Within strip [k-Delta, k]:
- Each column c contributes pp_c[i, c-i] for i in [max(0, c-n+1), min(c, n-1)]
  (the diagonal of vars producing partial products at that column).
- Cut(c) at diagonal c contains the "frontier" of UP-derived values:
  all acc_c[row, col] and cry_c[row, col] for col <= c in strip,
  and symmetric d vars.

Branching order: increasing column (diagonal), within diagonal by row.
Merging at diagonal boundaries on Cut(c).
"""

import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper_order import build_strip_all, propagate
from phase3_strip_extract import strip_delta


def diagonal_branch_order(cnf, k, delta, n):
    """Branch order: incoming carries, then by column, within column
    by row."""
    strip_cols = list(range(max(0, k - delta), k + 1))
    order = []
    added = set()

    # Incoming carries at col strip_start - 1.
    carry_boundary = strip_cols[0] - 1 if strip_cols else -1
    if carry_boundary >= 0:
        for side in ("c", "d"):
            tag = f"cry_{side}"
            for row in range(1, n):
                for v, role in cnf.meta.items():
                    if (role and role[0] == tag and role[1] == row
                            and role[2] == carry_boundary):
                        if v not in added:
                            order.append((-1, v))
                            added.add(v)
                        break

    # By column (= i+j diagonal), each column has pp_c[i, col-i] for
    # valid i.
    for col in strip_cols:
        for i in range(max(0, col - n + 1), min(col + 1, n)):
            j = col - i
            if 0 <= j < n:
                for v, role in cnf.meta.items():
                    if (role and role[0] == "pp_c"
                            and role[1] == i and role[2] == j):
                        if v not in added:
                            order.append((col, v))
                            added.add(v)
                        break

    # Output vars at end (for cols in strip).
    from phase3_bp_cut_v2 import get_output_var_for_col
    for col in strip_cols:
        for side in ("c", "d"):
            ov = get_output_var_for_col(cnf, side, col, n)
            if ov is not None and ov not in added:
                order.append((max(strip_cols) + 1, ov))
                added.add(ov)
    return order


def get_diagonal_state_vars(cnf, k, delta, n):
    """Cut(col) = all acc/cry/pp vars for col' <= col in strip.
    Cumulative. Safe merging. (Diagonal branch order still applies.)"""
    strip_cols = list(range(max(0, k - delta), k + 1))
    state_by_col = defaultdict(set)
    for v, role in cnf.meta.items():
        if not role:
            continue
        tag = role[0]
        if tag in ("acc_c", "acc_d", "cry_c", "cry_d"):
            row, col = role[1], role[2]
            if col in strip_cols:
                state_by_col[col].add(v)
        elif tag in ("pp_c", "pp_d"):
            i, j = role[1], role[2]
            col = i + j
            if col in strip_cols:
                state_by_col[col].add(v)
    return state_by_col


def build_bp_diag(n, k):
    cnf, strip_clauses, forced_e, delta = build_strip_all(n, k)
    branch_order = diagonal_branch_order(cnf, k, delta, n)
    state_by_col = get_diagonal_state_vars(cnf, k, delta, n)
    strip_cols = list(range(max(0, k - delta), k + 1))

    init_final, init_conflict = propagate(strip_clauses, forced_e)
    if init_conflict is not None:
        return {"root": None, "nodes": {}, "conflict": init_conflict,
                "flat_order": branch_order}

    def cut_sig(assign, up_to_col):
        """Return cumulative cut state for cols <= up_to_col in strip.
        Returns None if some cut var is unassigned."""
        if up_to_col < 0:
            return ()
        sig = []
        for c in strip_cols:
            if c > up_to_col:
                break
            for v in sorted(state_by_col.get(c, set())):
                if v in forced_e:
                    continue
                if v not in assign:
                    return None
                sig.append((v, assign[v]))
        return tuple(sig)

    root_key = (-2, cut_sig(init_final, -1) or (), 0)
    nodes = {root_key: None}
    frontier = [(init_final, root_key, 0)]

    while frontier:
        assign, key, fp = frontier.pop()
        if nodes.get(key) is not None and "var" in nodes.get(key, {}):
            continue
        while fp < len(branch_order) and branch_order[fp][1] in assign:
            fp += 1
        if fp >= len(branch_order):
            nodes[key] = {"stuck": True}
            continue
        tag, var = branch_order[fp]
        # Determine if this is last var at this "column tag".
        is_last_in_col = (
            fp + 1 >= len(branch_order)
            or branch_order[fp + 1][0] != tag
        )
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
                if is_last_in_col and tag >= 0:
                    sig = cut_sig(new_final, tag)
                    if sig is None:
                        sig = tuple(sorted(
                            (v, new_final[v]) for v in new_final
                            if v not in forced_e))
                    ck = (tag, sig, fp + 1)
                else:
                    assigned_state = tuple(sorted(
                        (v, new_final[v]) for v in new_final
                        if v not in forced_e))
                    ck = (tag, assigned_state, fp + 1)
                if ck not in nodes:
                    nodes[ck] = None
                    frontier.append((new_final, ck, fp + 1))
                children[bit] = ck
        nodes[key] = {"var": var, "children": children, "flat_pos": fp}
    return {"root": root_key, "nodes": nodes, "flat_order": branch_order}


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_diag.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    bp = build_bp_diag(n, k)
    if bp.get("conflict"):
        print(f"n={n}, k={k}: UP refutes at root")
        return
    total = len(bp["nodes"])
    leaves = sum(1 for i in bp["nodes"].values() if i and "leaf" in i)
    internal = sum(1 for i in bp["nodes"].values() if i and "var" in i)
    stuck = sum(1 for i in bp["nodes"].values() if i and "stuck" in i)
    print(f"n={n}, k={k}: Diag BP {total} nodes "
          f"(int={internal}, leaves={leaves}, stuck={stuck}), "
          f"|bo|={len(bp['flat_order'])}")


if __name__ == "__main__":
    main()
