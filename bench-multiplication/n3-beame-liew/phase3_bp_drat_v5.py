#!/usr/bin/env python3
"""
N3 Phase 3 step 2 v5: enumerate ALL branch_order assignments,
emit one cut per conflict, resolve via binary tree on
branch_order vars.

This is "Phase 1 but on branch_order variables instead of input
variables". It doesn't benefit from BP merging yet, but it should
validate with drat-trim and give a concrete upper bound.
"""

import itertools
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper_order import (
    build_strip_all, propagate, branching_vars_in_order,
)
from phase3_strip_extract import strip_delta


def emit_drat(n, k, out_path, cnf_path):
    cnf, strip_clauses, forced_e, delta = build_strip_all(n, k)
    bo = branching_vars_in_order(cnf, k, delta, n)

    # Enumerate branch_order assignments.
    # This is 2^|bo|, may be too large; abort if >1<<20.
    if len(bo) > 20:
        raise RuntimeError(f"|bo|={len(bo)} too large to enumerate")

    cuts = []
    for vals in itertools.product([False, True], repeat=len(bo)):
        assign = dict(forced_e)
        for v, val in zip(bo, vals):
            assign[v] = val
        _, conflict = propagate(strip_clauses, assign)
        if conflict is None:
            continue
        # Cut = negation of branch literals.
        cut = frozenset(-v if val else v for v, val in zip(bo, vals))
        cuts.append(cut)

    unique_cuts = set(cuts)
    # Write CNF.
    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, "w") as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(" ".join(str(l) for l in cl) + " 0\n")

    # Emit cuts.
    with open(out_path, "w") as f:
        emitted = set()
        for cut in unique_cuts:
            if not cut:
                continue
            sorted_lits = sorted(cut, key=lambda x: (abs(x), x))
            f.write(" ".join(str(l) for l in sorted_lits) + " 0\n")
            emitted.add(cut)

        # Resolve via binary tree on bo.
        current = set(unique_cuts)
        for v in bo:
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

    return len(unique_cuts), len(bo)


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_drat_v5.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf_path = f"/tmp/strip_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_n{n}_k{k}.drat"

    try:
        n_cuts, bo_size = emit_drat(n, k, drat_path, cnf_path)
    except RuntimeError as e:
        print(f"n={n}, k={k}: SKIP ({e})")
        return

    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n}, k={k}: |bo|={bo_size}, {n_cuts} unique cuts, "
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
