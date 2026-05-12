#!/usr/bin/env python3
"""
N3 Phase 3 step 2 v4: use BP's UP-saturated state as cut clauses,
one per (a, b) input pair.

Key insight: the BP's merging on (output, tableau) values means
many distinct (a, b) pairs may land at the same leaf with the
same UP state. When that happens, the cut clause is identical,
and we emit it once.

Algorithm:
  1. For each (a, b), propagate forced_e + (a, b) through strip CNF.
     Record conflict clause. UP-saturated assignment = "state".
  2. For each state, emit cut = NOT(state literals except forced_e).
  3. Dedupe cuts (states from different (a, b) may yield same cut).
  4. Resolve via binary tree on input variables (Phase 1 v2 style).

The number of UNIQUE cuts tells us the effective BP merge factor.
If <<2^(2n), we beat Phase 1.
"""

import itertools
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper_order import build_strip_all, propagate


def emit_drat(n, k, out_path, cnf_path):
    cnf, strip_clauses, forced_e, delta = build_strip_all(n, k)

    # Input vars.
    a_vars = sorted([v for v, r in cnf.meta.items() if r and r[0] == "a_bit"],
                    key=lambda v: cnf.meta[v][1])
    b_vars = sorted([v for v, r in cnf.meta.items() if r and r[0] == "b_bit"],
                    key=lambda v: cnf.meta[v][1])
    assert len(a_vars) == n and len(b_vars) == n

    # Enumerate (a, b).
    cuts = set()
    cut_to_inputs = defaultdict(list)
    for a_vals in itertools.product([False, True], repeat=n):
        for b_vals in itertools.product([False, True], repeat=n):
            assign = dict(forced_e)
            for v, val in zip(a_vars, a_vals):
                assign[v] = val
            for v, val in zip(b_vars, b_vals):
                assign[v] = val
            final, conflict = propagate(strip_clauses, assign)
            if conflict is None:
                # No conflict -- strip is SAT for this (a, b)?
                # Shouldn't happen for strip refutations, but handle.
                continue
            # Build cut from final's non-forced_e assignments.
            cut = frozenset(
                (-v if val else v)
                for v, val in final.items()
                if v not in forced_e
            )
            cuts.add(cut)
            cut_to_inputs[cut].append((a_vals, b_vals))

    # Write CNF.
    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, "w") as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(" ".join(str(l) for l in cl) + " 0\n")

    # Emit cuts.
    with open(out_path, "w") as f:
        emitted = set()
        for cut in cuts:
            sorted_lits = sorted(cut, key=lambda x: (abs(x), x))
            if not sorted_lits:
                continue
            if cut in emitted:
                continue
            f.write(" ".join(str(l) for l in sorted_lits) + " 0\n")
            emitted.add(cut)

        # Resolve via binary tree on input variables, then all cut vars.
        all_cut_vars = set()
        for cut in cuts:
            for lit in cut:
                all_cut_vars.add(abs(lit))
        # Order: input vars first (a, b), then others.
        resolve_order = []
        for v in a_vars + b_vars:
            if v in all_cut_vars:
                resolve_order.append(v)
        for v in sorted(all_cut_vars):
            if v not in resolve_order:
                resolve_order.append(v)

        current = set(cuts)
        for v in resolve_order:
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

    return len(cuts), len(cut_to_inputs)


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_drat_v4.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf_path = f"/tmp/strip_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_n{n}_k{k}.drat"

    n_cuts, n_inputs = emit_drat(n, k, drat_path, cnf_path)

    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n}, k={k}: {n_cuts} unique cuts (from {2**(2*n)} inputs), "
          f"CNF {cnf_bytes}B, DRAT {drat_bytes}B ({drat_lines} lemmas)")

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
