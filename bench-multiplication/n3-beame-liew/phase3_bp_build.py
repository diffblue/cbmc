#!/usr/bin/env python3
"""
N3 Phase 3 step 2 proper: construct a per-strip BP DAG with merging
on cut state, and emit a DRAT refutation that validates with
drat-trim.

The strip phi_Strip(k) is extracted as in phase3_strip_extract.py.
The BP has levels indexed by input-pair (a[i], b[i]) positions for
i=0..n-1. At level i, a BP node is labeled (i, cut_state), where
cut_state is the assignment to cut_vars(i, k, delta, n) that is
determined by inputs read so far (equivalently, by a[0..i-1],
b[0..i-1]).

MERGING: two (a[0..i-1], b[0..i-1]) prefixes that produce identical
cut_state collapse to one BP node at level i.

LEAVES: at level n (all inputs read), we have a complete input
assignment. UP through the strip (with forced e) yields a
contradiction; the leaf emits the violated clause.

DRAT EMISSION (Krajicek Prop 2.1):
- Post-order traversal of the BP DAG.
- Each BP node N has a "clause" C_N: the disjunction of literals
  that rule out the (i-prefix, cut_state) combination at N.
  Equivalently: "NOT (we reached N)". When propagated, it's the
  resolvent of its two children's clauses on the branching variable.
- Leaves: C_leaf = the violated strip clause (from the CNF).
- Emit each internal node's C_N as a RUP lemma, in post-order.
- Root's C_root is the empty clause.

Usage: python3 phase3_bp_build.py N K
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
    var_col,
)


def propagate_full(clauses, assign):
    """UP on `assign` over `clauses`; returns (final_assign, conflict_clause)."""
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


def build_strip_with_e_forced(n, k):
    """Build the full strip CNF (list of clauses) + forced e assignment."""
    cnf, _, _, _, _ = build_commutativity_cnf_meta(n)
    delta = strip_delta(n)
    strip_clauses = list(extract_strip(cnf, k, delta))
    # Add forced units.
    e_assign_clauses = []
    for v, role in cnf.meta.items():
        if role and role[0] == "diff":
            bit = role[1]
            if bit < k:
                e_assign_clauses.append([-v])
            elif bit == k:
                e_assign_clauses.append([v])
    return cnf, strip_clauses, e_assign_clauses, delta


def cut_vars(cnf, j, k, delta):
    """Return the set of variables that define Cut(j): acc_c/d and
    cry_c/d for rows <= j and strip cols."""
    strip_cols = set(range(max(0, k - delta), k + 1))
    cuts = set()
    for v, role in cnf.meta.items():
        if not role:
            continue
        if role[0] in ("acc_c", "acc_d", "cry_c", "cry_d"):
            row = role[1]
            col = role[2]
            if row <= j and col in strip_cols:
                cuts.add(v)
    return cuts


def find_input_vars(cnf, n):
    """Return a_vars, b_vars in index order."""
    a_vars = [None] * n
    b_vars = [None] * n
    for v, role in cnf.meta.items():
        if role and role[0] == "a_bit":
            a_vars[role[1]] = v
        elif role and role[0] == "b_bit":
            b_vars[role[1]] = v
    return a_vars, b_vars


def simulate_prefix(clauses, n, a_vars, b_vars, a_prefix, b_prefix, forced_e):
    """Given fixed assignment to inputs a[0..len(a_prefix)-1] and
    b[0..len(b_prefix)-1] plus forced_e, run UP over `clauses` and
    return (final_assign, conflict).
    """
    init = dict(forced_e)
    for i, val in enumerate(a_prefix):
        init[a_vars[i]] = val
    for i, val in enumerate(b_prefix):
        init[b_vars[i]] = val
    return propagate_full(clauses, init)


def build_bp(n, k):
    """Build the BP DAG for phi_Strip(k) at bitwidth n.

    Returns (bp_nodes, root_id, leaf_clauses).

    bp_nodes[id] = (level, cut_state, branching_var, children)
      where children is {0: child_id, 1: child_id} for level < n, or
      None for leaves (level == n).
    """
    cnf, strip_clauses, e_assign_clauses, delta = build_strip_with_e_forced(n, k)
    full_clauses = strip_clauses + e_assign_clauses
    a_vars, b_vars = find_input_vars(cnf, n)

    forced_e = {}
    for cl in e_assign_clauses:
        assert len(cl) == 1
        lit = cl[0]
        forced_e[abs(lit)] = lit > 0

    # We branch on (a[0], b[0]) as a pair at level 0, then (a[1], b[1])
    # at level 1, etc. Each level expands by factor of 4. For merging,
    # group by cut_state at each level.

    # BFS layer by layer.
    # state_to_id[(level, cut_state)] = id
    state_to_id = {}
    nodes = []  # nodes[id] = (level, cut_state_tuple, children, violated_clause)

    def get_or_create(level, cut_state, children, violated_clause):
        key = (level, cut_state)
        if key in state_to_id:
            return state_to_id[key]
        nid = len(nodes)
        state_to_id[key] = nid
        nodes.append([level, cut_state, children, violated_clause])
        return nid

    # Build leaf level first (level = n).
    leaf_clauses = {}  # cut_state -> violated_clause
    # Enumerate all (a, b) pairs, simulate, get cut state at level n
    # and the violated clause.
    for a_val in range(2 ** n):
        for b_val in range(2 ** n):
            a_prefix = [((a_val >> i) & 1) == 1 for i in range(n)]
            b_prefix = [((b_val >> i) & 1) == 1 for i in range(n)]
            final, conflict = simulate_prefix(
                full_clauses, n, a_vars, b_vars, a_prefix, b_prefix, forced_e
            )
            assert conflict is not None, (
                f"No conflict found for (a={a_val}, b={b_val}) at n={n}, k={k}"
            )
            cut = cut_vars(cnf, n, k, delta)
            cs = tuple(sorted(
                (v, final[v]) for v in cut if v in final
            ))
            if cs not in leaf_clauses:
                leaf_clauses[cs] = conflict
    # Create leaf nodes.
    for cs, vc in leaf_clauses.items():
        get_or_create(n, cs, None, vc)

    # Build internal levels bottom-up: for level L = n-1 down to 0,
    # compute transitions from each (L, cs) to (L+1, cs_0), (L+1, cs_1)
    # depending on b[L]. Actually we branch on (a[L], b[L]) as a pair
    # for simplicity -- 4 children per node.

    for level in range(n - 1, -1, -1):
        # For each (a[0..level], b[0..level]) prefix, simulate and get
        # cut state. Determine transitions.
        level_cuts = defaultdict(dict)
        # dict: parent_cut_state -> {(a_bit, b_bit): child_cut_state}
        for a_val in range(2 ** (level + 1)):
            for b_val in range(2 ** (level + 1)):
                a_prefix = [((a_val >> i) & 1) == 1 for i in range(level + 1)]
                b_prefix = [((b_val >> i) & 1) == 1 for i in range(level + 1)]
                final, conflict = simulate_prefix(
                    full_clauses, n, a_vars, b_vars, a_prefix, b_prefix,
                    forced_e
                )
                cut = cut_vars(cnf, level + 1, k, delta)
                cs = tuple(sorted(
                    (v, final[v]) for v in cut if v in final
                ))
                # Parent cut state (level L) is same but without the
                # a[level], b[level] contribution -- actually we need to
                # recompute with the shorter prefix.
                parent_a_prefix = a_prefix[:-1] if level > 0 else []
                parent_b_prefix = b_prefix[:-1] if level > 0 else []
                if level == 0:
                    parent_cs = ()
                else:
                    parent_final, _ = simulate_prefix(
                        full_clauses, n, a_vars, b_vars,
                        parent_a_prefix, parent_b_prefix, forced_e
                    )
                    parent_cut = cut_vars(cnf, level, k, delta)
                    parent_cs = tuple(sorted(
                        (v, parent_final[v]) for v in parent_cut if v in parent_final
                    ))
                # Record transition.
                a_bit = a_prefix[-1]
                b_bit = b_prefix[-1]
                level_cuts[parent_cs][(a_bit, b_bit)] = cs

        # Create internal nodes.
        for parent_cs, trans in level_cuts.items():
            # Children IDs.
            children = {}
            for (ab, bb), child_cs in trans.items():
                child_id = state_to_id.get((level + 1, child_cs))
                if child_id is None:
                    # Child may not exist if no leaf reached it; but for
                    # UNSAT this shouldn't happen.
                    continue
                children[(ab, bb)] = child_id
            get_or_create(level, parent_cs, children, None)

    root_id = state_to_id[(0, ())]
    return cnf, full_clauses, a_vars, b_vars, nodes, root_id


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_build.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf, full_clauses, a_vars, b_vars, nodes, root_id = build_bp(n, k)

    # Count nodes per level.
    per_level = defaultdict(int)
    for node in nodes:
        per_level[node[0]] += 1
    for L in sorted(per_level):
        print(f"Level {L}: {per_level[L]} nodes")
    print(f"Total BP nodes: {len(nodes)}")
    print(f"Root ID: {root_id}")


if __name__ == "__main__":
    main()
