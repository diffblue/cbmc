#!/usr/bin/env python3
"""
N3 Phase 3 Cut(j)-merging BP (v2).

Fixed implementation of row-by-row branching with Cut(j)-based
merging. Key corrections:

1. Output variables:
   For my ripple-carry multiplier:
   - col 0: pp_c[0, 0]
   - col in [1, n-1]: acc_c[col, col]  (last FA at row=col, j=0)
   - col in [n, 2n-1]: acc_c[n-1, col] (last touch at final HA row)

2. Branching order (paper-aligned):
   a) For each row i from 0 to n-1:
        branch on tableau pp_c[i, j] for (i+j) in strip range
   b) Between rows, UP propagates and computes acc_c, cry_c, etc.

3. State merging at row boundary:
   state = {acc_c[i, col], cry_c[i, col] for col in strip range,
            symmetric for d}
   Only these matter for downstream computation.

Expected: polynomial BP size since |state| = O(log k) -> poly(k)
distinct states.
"""

import itertools
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper_order import build_strip_all, propagate
from phase3_strip_extract import strip_delta
from generate_array_mul_comm_meta import build_commutativity_cnf_meta


def get_row_state_vars(cnf, k, delta, n):
    """Cut(row) = {acc_c[row, col], cry_c[row, col+1] : col in strip}
                  UNION symmetric for d.

    Returns: dict row -> set of vars that form the state at end of row.

    Special case for ripple-carry row 0: acc_c[0, col] = pp_c[0, col]
    (no separate acc_c[0, *] vars). So Cut(0) = {pp_c[0, col], pp_d[0, col]}
    for col in strip (plus ZERO constants, but those are forced).
    """
    strip_cols = list(range(max(0, k - delta), k + 1))
    # Include one extra col for carry (cry at col c is between col c-1 and c).
    carry_cols = list(range(max(0, k - delta), k + 2))
    state_by_row = defaultdict(set)
    for v, role in cnf.meta.items():
        if not role:
            continue
        tag = role[0]
        if tag in ("acc_c", "acc_d"):
            row, col = role[1], role[2]
            if col in strip_cols:
                state_by_row[row].add(v)
        if tag in ("cry_c", "cry_d"):
            row, col = role[1], role[2]
            if col in carry_cols:
                state_by_row[row].add(v)
        # Row 0 accumulator is pp_c[0, *] (ripple-carry specific).
        if tag in ("pp_c", "pp_d") and role[1] == 0:
            col = role[2]
            if col in strip_cols:
                state_by_row[0].add(v)
    return state_by_row


def tableau_vars_by_row(cnf, k, delta, n):
    """Returns dict row -> list of pp_c[row, j] vars with row+j in strip."""
    strip_cols = list(range(max(0, k - delta), k + 1))
    tab_by_row = defaultdict(list)
    for v, role in cnf.meta.items():
        if role and role[0] == "pp_c":
            i, j = role[1], role[2]
            if (i + j) in strip_cols:
                tab_by_row[i].append(v)
    for r in tab_by_row:
        tab_by_row[r].sort()
    return tab_by_row


def get_output_var_for_col(cnf, side, col, n):
    """For ripple-carry multiplier:
       col 0 -> pp_{side}[0, 0]
       col in [1, n-1] -> acc_{side}[col, col]
       col in [n, 2n-1] -> acc_{side}[n-1, col]
    """
    tag_pp = f"pp_{side}"
    tag_acc = f"acc_{side}"
    if col == 0:
        for v, role in cnf.meta.items():
            if role and role[0] == tag_pp and role[1] == 0 and role[2] == 0:
                return v
    elif 1 <= col < n:
        for v, role in cnf.meta.items():
            if (role and role[0] == tag_acc
                    and role[1] == col and role[2] == col):
                return v
    else:  # col in [n, 2n-1]
        for v, role in cnf.meta.items():
            if (role and role[0] == tag_acc
                    and role[1] == n - 1 and role[2] == col):
                return v
    return None


def build_bp_cut_rows(n, k):
    """Build BP with row-by-row tableau branching and Cut(row)
    state merging at row boundaries.

    Within a row, all tableau branches are done without merging.
    At row boundary, state_key = (row, Cut(row)) merges states.
    """
    cnf, strip_clauses, forced_e, delta = build_strip_all(n, k)
    tab_by_row = tableau_vars_by_row(cnf, k, delta, n)
    state_by_row = get_row_state_vars(cnf, k, delta, n)

    # Initial propagation.
    init_final, init_conflict = propagate(strip_clauses, forced_e)

    # Node key: (row, state_sig).
    # Within a row, we branch on all tab_by_row[row] vars in order.
    # Intermediate nodes (partway through a row) have their own keys
    # based on "progress within row".

    # Use BFS. A node_key = (row, state_sig, progress_within_row).
    # progress_within_row = # tab vars already branched in current row.

    def state_sig(assign, up_to_row):
        # State signature = values of acc/cry vars for all rows <= up_to_row.
        # Returns None if any Cut(r) var for r <= up_to_row is unassigned
        # (in which case we don't merge -- the state is path-specific).
        sig = []
        for r in range(up_to_row + 1):
            for v in sorted(state_by_row.get(r, set())):
                if v in forced_e:
                    continue
                if v not in assign:
                    return None  # Cannot merge safely.
                sig.append((v, assign[v]))
        return tuple(sig)

    nodes = {}
    # Start from root.
    if init_conflict is not None:
        return {"root": None, "nodes": {}, "conflict": init_conflict}

    # Flatten branching: for each row, its tab vars in order.
    # Plus OUTPUT vars (c[col] and d[col] for col in strip) at the end.
    # Outputs are branched LAST so that tableau branching triggers
    # UP to determine accumulator state; outputs cover remaining
    # freedom.
    strip_cols = list(range(max(0, k - delta), k + 1))
    flat_order = []
    # (0) Incoming carries at col strip_start - 1 (boundary from
    #     outside strip). For each row i in [1, n-1] and both
    #     sides.
    carry_boundary = strip_cols[0] - 1 if strip_cols else -1
    added_vars = set()
    if carry_boundary >= 0:
        for side in ("c", "d"):
            tag = f"cry_{side}"
            for row in range(1, n):
                for v, role in cnf.meta.items():
                    if (role and role[0] == tag
                            and role[1] == row
                            and role[2] == carry_boundary):
                        if v not in added_vars:
                            flat_order.append((-1, v))  # row=-1 tag
                            added_vars.add(v)
                        break
    for row in sorted(tab_by_row):
        for v in tab_by_row[row]:
            if v not in added_vars:
                flat_order.append((row, v))
                added_vars.add(v)
    # Add output vars (as "row = n" tag, branched after all tableau).
    output_vars = []
    for col in strip_cols:
        for side in ("c", "d"):
            ov = get_output_var_for_col(cnf, side, col, n)
            if ov is not None and ov not in added_vars:
                output_vars.append(ov)
                flat_order.append((n, ov))
                added_vars.add(ov)

    root_key = (0, state_sig(init_final, -1), 0)
    nodes[root_key] = None
    frontier = [(init_final, root_key, 0)]

    while frontier:
        assign, key, flat_pos = frontier.pop()
        if nodes.get(key) is not None and "var" in nodes.get(key, {}):
            continue
        # Skip already-assigned vars.
        while flat_pos < len(flat_order) and flat_order[flat_pos][1] in assign:
            flat_pos += 1
        if flat_pos >= len(flat_order):
            nodes[key] = {"stuck": True}
            continue
        cur_row, var = flat_order[flat_pos]
        # Determine if crossing a row boundary:
        # After this branch + UP, are we at "end of row cur_row"?
        is_last_in_row = (
            flat_pos + 1 >= len(flat_order)
            or flat_order[flat_pos + 1][0] != cur_row
        )
        children = {}
        for bit in (False, True):
            new_assign = dict(assign)
            new_assign[var] = bit
            new_final, conflict = propagate(strip_clauses, new_assign)
            if conflict is not None:
                leaf_key = ("leaf", tuple(conflict), flat_pos)
                # Dedupe leaves with same conflict clause, regardless of
                # position. Use just the conflict tuple.
                leaf_key = ("leaf", tuple(conflict))
                nodes[leaf_key] = {"leaf": list(conflict)}
                children[bit] = leaf_key
            else:
                if is_last_in_row and cur_row >= 0:
                    # Row boundary: merge on (cur_row, state_sig(up to cur_row))
                    # IF all Cut(cur_row) vars are assigned.
                    # cur_row >= 0 guard: row -1 (incoming carries) doesn't
                    # correspond to a real cut level; no merging there.
                    sig = state_sig(new_final, cur_row)
                    if sig is None:
                        # Can't merge safely; use full assignment.
                        sig = tuple(
                            sorted((v, new_final[v]) for v in new_final
                                   if v not in forced_e)
                        )
                    ck = (cur_row, sig, flat_pos + 1)
                else:
                    # Within-row OR row -1 (incoming carries):
                    # use full assign so far (no merging).
                    assigned_state = tuple(
                        sorted((v, new_final[v]) for v in new_final
                               if v not in forced_e)
                    )
                    ck = (cur_row, assigned_state, flat_pos + 1)
                if ck not in nodes:
                    nodes[ck] = None
                    frontier.append((new_final, ck, flat_pos + 1))
                children[bit] = ck
        nodes[key] = {"var": var, "children": children, "flat_pos": flat_pos}

    return {"root": root_key, "nodes": nodes, "flat_order": flat_order,
            "state_by_row": state_by_row}


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_cut_v2.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    bp = build_bp_cut_rows(n, k)
    if bp.get("conflict"):
        print(f"n={n}, k={k}: UP refutes at root")
        return

    total = len(bp["nodes"])
    leaves = sum(1 for i in bp["nodes"].values() if i and "leaf" in i)
    internal = sum(1 for i in bp["nodes"].values() if i and "var" in i)
    stuck = sum(1 for i in bp["nodes"].values() if i and "stuck" in i)
    nones = sum(1 for i in bp["nodes"].values() if i is None)
    print(f"n={n}, k={k}: Cut-rows BP {total} nodes "
          f"(int={internal}, leaves={leaves}, stuck={stuck}, none={nones}), "
          f"|flat|={len(bp['flat_order'])}")


if __name__ == "__main__":
    main()
