#!/usr/bin/env python3
"""
N3 Phase 3 step 2 DRAT emission (v3): use the full UP-derived
assignment at each leaf as the cut clause.

This is less elegant than pure resolution but guaranteed RUP-valid:
if UP at assignment `a` derives a conflict, then the cut clause
"NOT a" is RUP-derivable by the same UP.

We still get merging benefit because the BP's path-to-leaf is
captured in one cut clause (covering all (a, b) pairs that reach
that leaf's UP state).

After emitting cuts, we resolve them via the paper-order branch
variables in a binary tree (same as Phase 1 v2) to produce the
empty clause.
"""

import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper_order import build_bp, build_strip_all, propagate
from phase3_strip_extract import strip_delta


def cut_from_assign(assign, forced_e):
    """Return a frozenset of literals negating `assign` (excluding
    forced_e which is a constant across the whole proof)."""
    lits = []
    for v, val in assign.items():
        if v in forced_e:
            continue
        lits.append(-v if val else v)
    return frozenset(lits)


def collect_leaf_cuts(n, k):
    """Re-do the BP enumeration, but record at each leaf the full
    UP-saturated assignment (excluding forced_e) as a cut clause.
    Returns the set of unique cut clauses."""
    cnf, strip_clauses, forced_e, branch_order, bp = build_bp(n, k)

    # The BP nodes store the branching var and children, but not the
    # full UP state. We need to re-traverse and re-propagate along
    # each path.
    unique_cuts = set()
    nodes = bp["nodes"]

    def dfs(node_key, partial_assign):
        info = nodes[node_key]
        if "leaf" in info:
            # partial_assign should already cause UP conflict.
            final, conflict = propagate(strip_clauses, partial_assign)
            assert conflict is not None, (
                f"Expected conflict at leaf, partial={partial_assign}"
            )
            unique_cuts.add(cut_from_assign(final, forced_e))
            return
        if "stuck" in info:
            return
        var = info["var"]
        for val in (False, True):
            new_assign = dict(partial_assign)
            new_assign[var] = val
            new_final, conflict = propagate(strip_clauses, new_assign)
            if conflict is not None:
                unique_cuts.add(cut_from_assign(new_final, forced_e))
                continue
            child_key = info["children"][val]
            dfs(child_key, new_final)

    # Start from root with forced_e propagated.
    init_final, init_conflict = propagate(strip_clauses, forced_e)
    if init_conflict is not None:
        unique_cuts.add(cut_from_assign(init_final, forced_e))
    else:
        dfs(bp["root_state"], init_final)

    return cnf, strip_clauses, forced_e, branch_order, unique_cuts


def emit_drat_with_resolution(n, k, out_path):
    cnf, strip_clauses, forced_e, branch_order, unique_cuts = collect_leaf_cuts(n, k)

    # All variables that appear in any cut clause get resolved in order.
    all_vars = set()
    for cc in unique_cuts:
        for lit in cc:
            all_vars.add(abs(lit))
    # Order: use branch_order first (for those vars), then any others.
    ordered_vars = []
    seen = set()
    for v in branch_order:
        if v in all_vars and v not in seen:
            ordered_vars.append(v)
            seen.add(v)
    for v in sorted(all_vars):
        if v not in seen:
            ordered_vars.append(v)

    with open(out_path, "w") as f:
        emitted = set()
        for cc in unique_cuts:
            if cc in emitted:
                continue
            sorted_lits = sorted(cc, key=lambda x: (abs(x), x))
            if not sorted_lits:
                continue
            f.write(" ".join(str(l) for l in sorted_lits) + " 0\n")
            emitted.add(cc)

        current = set(unique_cuts)
        for v in ordered_vars:
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
        # Emit empty clause.
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
        print("usage: phase3_bp_drat_v3.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf_path = f"/tmp/strip_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_n{n}_k{k}.drat"
    write_strip_cnf(n, k, cnf_path)
    emit_drat_with_resolution(n, k, drat_path)

    drat_bytes = os.path.getsize(drat_path)
    cnf_bytes = os.path.getsize(cnf_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n}, k={k}: CNF {cnf_bytes}B, DRAT {drat_bytes}B "
          f"({drat_lines} lemmas)")

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
