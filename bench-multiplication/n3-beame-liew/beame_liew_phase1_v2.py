#!/usr/bin/env python3
"""
N3 Phase 1 prototype: generate a Beame-Liew-style DRAT refutation for
the commutativity formula a*b = b*a on an n-bit array multiplier.

Proof strategy:
  1. Case-split on every (a, b) assignment (2^(2n) leaves).
  2. On each leaf, unit propagation on the original CNF derives the
     empty clause. Emit the corresponding "branch negation" cut clause
     C_(a*,b*) = (NOT a_0=a*_0 OR ... OR NOT b_{n-1}=b*_{n-1}), which
     is a valid RUP lemma (RUP starts from NOT C = a=a*, b=b* and
     propagates through the CNF to conflict).
  3. Merge the 2^(2n) leaf clauses pairwise via a binary resolution
     tree, each resolution step being a shorter RUP-valid lemma,
     until we reach the empty clause.

This is not the asymptotically polynomial Beame-Liew critical-strip
refutation; it is an O(2^(2n)) case-analysis proof that demonstrates
the mechanics (UP-on-leaf + structured merging) on which Beame-Liew's
construction depends. Validated by drat-trim.

Usage: python3 beame_liew_phase1_v2.py N
"""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from generate_array_mul_comm import build_commutativity_cnf


def propagate(cnf_clauses, assign):
    """Unit-propagate `assign` through `cnf_clauses` in place.

    Returns (assign, conflict_clause) where conflict_clause is None if
    propagation reached a fixpoint without conflict, otherwise the
    first clause that became falsified.
    """
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


def leaf_is_unsat(cnf_clauses, a_vars, b_vars, a_val, b_val):
    """Confirm that under a=a_val, b=b_val, the CNF is UNSAT via UP."""
    assign = {}
    for i, v in enumerate(a_vars):
        assign[v] = ((a_val >> i) & 1) == 1
    for i, v in enumerate(b_vars):
        assign[v] = ((b_val >> i) & 1) == 1
    _, conflict = propagate(cnf_clauses, assign)
    return conflict is not None


def branch_cut_literals(a_vars, b_vars, a_val, b_val):
    """Return the DIMACS literals of C_(a*,b*) = "NOT this branch"."""
    lits = []
    for i, v in enumerate(a_vars):
        val = (a_val >> i) & 1
        lits.append(-v if val else v)
    for i, v in enumerate(b_vars):
        val = (b_val >> i) & 1
        lits.append(-v if val else v)
    return lits


def emit_drat_proof(n, drat_out):
    """Emit a DRAT proof of UNSAT for the comm formula at width n.

    Emitted in three phases:
      (a) 2^(2n) leaf cut clauses, one per (a, b) branch.
      (b) binary resolution tree over input-bit variables: for each
          input variable, resolve pairs of clauses that differ only in
          that variable's polarity, producing clauses of length
          one less.
      (c) empty clause.

    All lemmas are RUP-valid in the accumulating clause set.
    """
    cnf, a_vars, b_vars, c_vars, d_vars = build_commutativity_cnf(n)

    # -- Phase A: emit all 2^(2n) cut clauses. --
    cuts = {}  # frozenset of lits -> the DIMACS-ordered list of lits
    for a_val in range(2 ** n):
        for b_val in range(2 ** n):
            assert leaf_is_unsat(cnf.clauses, a_vars, b_vars, a_val, b_val)
            lits = branch_cut_literals(a_vars, b_vars, a_val, b_val)
            cuts[frozenset(lits)] = lits
            drat_out.write(" ".join(str(x) for x in lits) + " 0\n")

    # -- Phase B: binary-resolution tree. --
    # Order: for each variable (a_0, a_1, ..., b_0, ..., b_{n-1}) in turn,
    # pair clauses that differ only in that variable's polarity; emit
    # the resolvent (which drops that variable).
    input_vars = list(a_vars) + list(b_vars)  # elim in this order
    current = set(cuts.keys())  # set of frozensets
    for v in input_vars:
        next_set = set()
        # Partition current by clauses containing +v, -v, or neither.
        pos = {}  # rest_frozenset -> full frozenset containing +v
        neg = {}
        for cls in current:
            if v in cls:
                pos[frozenset(cls - {v})] = cls
            elif -v in cls:
                neg[frozenset(cls - {-v})] = cls
            else:
                # v not in clause (shouldn't happen at this stage).
                next_set.add(cls)
        # Pair clauses with the same "rest" but opposite polarity.
        for rest, pos_cls in pos.items():
            if rest in neg:
                # Emit the resolvent (which is just `rest`).
                resolvent_lits = sorted(rest, key=lambda x: (abs(x), x))
                if resolvent_lits:
                    drat_out.write(
                        " ".join(str(x) for x in resolvent_lits) + " 0\n"
                    )
                else:
                    # Empty resolvent — the empty clause.
                    drat_out.write("0\n")
                next_set.add(rest)
            else:
                # No match: keep the pos clause.
                next_set.add(pos_cls)
        for rest, neg_cls in neg.items():
            if rest not in pos:
                next_set.add(neg_cls)
        current = next_set

    # After eliminating all 2n input variables, `current` should contain
    # exactly the empty clause. If not, emit it explicitly for safety
    # (the solver may require an explicit terminator).
    if frozenset() not in current:
        drat_out.write("0\n")

    return cnf


def main():
    if len(sys.argv) < 2:
        print("usage: beame_liew_phase1_v2.py N", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    cnf_path = f"/tmp/comm_n{n}_bl.cnf"
    drat_path = f"/tmp/comm_n{n}_bl.drat"

    with open(drat_path, "w") as f:
        cnf = emit_drat_proof(n, f)

    with open(cnf_path, "w") as f:
        cnf.write(f)

    drat_size = os.path.getsize(drat_path)
    cnf_size = os.path.getsize(cnf_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n}: CNF {cnf_size} bytes ({cnf.next_var - 1} vars, "
          f"{len(cnf.clauses)} clauses)")
    print(f"n={n}: DRAT {drat_size} bytes ({drat_lines} lines)")


if __name__ == "__main__":
    main()
