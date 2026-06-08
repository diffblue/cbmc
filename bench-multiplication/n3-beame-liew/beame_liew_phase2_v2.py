#!/usr/bin/env python3
"""
N3 Phase 2 structural attempt (column-organized DRAT).

Goal: produce a DRAT proof whose STRUCTURE makes explicit the
column-by-column decomposition implicit in the Beame-Liew
critical-strip construction, even if the total size is not
polynomial.

Structure:
  1. Enumerate all 4^n input assignments to (a, b). For each, UP
     through the CNF determines every internal variable, including
     diff[0..2n-1] (all False, because commutativity holds).
  2. For each input assignment, emit ONE cut clause per column k:
     (NOT input-branch OR -diff[k]).  That is 4^n * 2n cut clauses.
  3. For each column k independently, resolve the 4^n cut clauses
     down to the unit `-diff[k]`.
  4. After all 2n units are present, the `diff[0] OR ... OR diff[2n-1]`
     clause UP-contradicts.

Comparison to Phase 1:
  - Phase 1 size: 4^n leaf clauses of length 2n + resolution tree = O(n * 4^n).
  - This Phase 2: 2n * 4^n leaf clauses of length 2n + 2n * (4^n - 1)
    internal nodes + 2n units = O(n^2 * 4^n).
  - So this is STRICTLY larger than Phase 1 by roughly a factor of n.
  - But the proof is column-organized: the sub-proof for each column
    k is a self-contained refutation that diff[k] = False.

This prototype demonstrates the column decomposition; it is NOT the
polynomial-size Beame-Liew refutation.

Usage: python3 beame_liew_phase2_v2.py N
"""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from generate_array_mul_comm_meta import build_commutativity_cnf_meta


def propagate(cnf_clauses, assign):
    changed = True
    while changed:
        changed = False
        for cl in cnf_clauses:
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


def find_diff_vars(cnf):
    diff = {}
    for v, role in cnf.meta.items():
        if role and role[0] == "diff":
            diff[role[1]] = v
    if not diff:
        return []
    n_out = max(diff) + 1
    return [diff[k] for k in range(n_out)]


def emit_proof(n, drat_path, cnf_path):
    cnf, a_vars, b_vars, c_vars, d_vars = build_commutativity_cnf_meta(n)
    diff_vars = find_diff_vars(cnf)
    assert len(diff_vars) == 2 * n

    # Full enumeration of (a, b). For each, compute diff[k] (all False).
    # Emit 2n cut clauses per assignment (one per output bit).
    all_branch_lits = {}  # (a_val, b_val) -> list of DIMACS literals encoding NOT this branch
    for a_val in range(2 ** n):
        for b_val in range(2 ** n):
            # Sanity: propagate and check all diff[k] = False.
            assign = {}
            for i, v in enumerate(a_vars):
                assign[v] = ((a_val >> i) & 1) == 1
            for i, v in enumerate(b_vars):
                assign[v] = ((b_val >> i) & 1) == 1
            _, conflict = propagate(cnf.clauses, assign)
            # We expect UP to derive all diff[k] = False, which triggers
            # the "at least one diff" clause -> conflict.
            assert conflict is not None, (
                f"No conflict under full assignment a={a_val}, b={b_val}"
            )
            for k in range(2 * n):
                if diff_vars[k] in assign:
                    assert assign[diff_vars[k]] is False, (
                        f"diff[{k}] != False under (a={a_val}, b={b_val})"
                    )
            # Collect branch literals.
            branch_lits = []
            for i, v in enumerate(a_vars):
                val = (a_val >> i) & 1
                branch_lits.append(-v if val else v)
            for i, v in enumerate(b_vars):
                val = (b_val >> i) & 1
                branch_lits.append(-v if val else v)
            all_branch_lits[(a_val, b_val)] = branch_lits

    with open(cnf_path, "w") as f:
        cnf.write(f)

    # Emit per-column proof of -diff[k].
    with open(drat_path, "w") as f:
        for k in range(2 * n):
            # (a) Emit 4^n cut clauses (NOT branch OR -diff[k]).
            cuts = set()
            for (a_val, b_val), branch in all_branch_lits.items():
                cut = branch + [-diff_vars[k]]
                cut_frozen = frozenset(cut)
                cuts.add(cut_frozen)
                f.write(" ".join(str(x) for x in cut) + " 0\n")
            # (b) Binary resolution tree over the input variables to
            #     collapse the 4^n cuts into the unit `-diff[k]`.
            input_vars = list(a_vars) + list(b_vars)
            current = set(cuts)
            for v in input_vars:
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
                        if resolvent:
                            f.write(" ".join(str(x) for x in resolvent) + " 0\n")
                        next_set.add(rest)
                    else:
                        next_set.add(pos_cls)
                for rest, neg_cls in neg.items():
                    if rest not in pos:
                        next_set.add(neg_cls)
                current = next_set
        # After all -diff[k] units, UP on the "diff OR" clause contradicts.
        f.write("0\n")

    return cnf


def main():
    if len(sys.argv) < 2:
        print("usage: beame_liew_phase2_v2.py N", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    cnf_path = f"/tmp/comm_n{n}_bl2.cnf"
    drat_path = f"/tmp/comm_n{n}_bl2.drat"

    cnf = emit_proof(n, drat_path, cnf_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    drat_bytes = os.path.getsize(drat_path)
    cnf_bytes = os.path.getsize(cnf_path)
    print(f"n={n}: CNF {cnf_bytes} bytes ({cnf.next_var - 1} vars, "
          f"{len(cnf.clauses)} clauses)")
    print(f"n={n}: DRAT {drat_bytes} bytes ({drat_lines} lines)")


if __name__ == "__main__":
    main()
