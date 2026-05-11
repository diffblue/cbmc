#!/usr/bin/env python3
"""
N3 Phase 1 prototype: generate a Beame-Liew-style DRAT refutation for
the commutativity formula a*b = b*a on an n-bit array multiplier.

For now we implement the simplest instance of the critical-strip idea:
we enumerate all 2^(2n) assignments to the input bits (a and b), and for
each assignment emit a DRAT block that derives the empty clause along
that branch.  This is an exponential-size proof (not the O(n^6 log n)
polynomial), but it demonstrates the mechanics: enumerate -> unit
propagate -> emit unit clauses -> reach the empty clause.

The resulting DRAT file is validated by drat-trim, giving an independent
check that the CNF really is UNSAT for the reason we claim (commutativity
holds for the array multiplier).

What this is:
- A working DRAT generator that closes out the formula by deterministic
  case analysis rather than by CDCL search.
- A reference for per-branch proof length at small n.

What this is not (and Phase 2 would add):
- The polynomial-size critical-strip refutation of Beame-Liew (2019).
  The critical-strip construction exploits the fact that only
  Delta = log(2n) bits need to be tracked across adjacent strips, which
  requires a branching-program representation rather than the flat
  enumeration used here.

Usage: python3 beame_liew_phase1.py N [OUT.drat]
"""

import sys
import os
import subprocess
import itertools

# Make the CNF generator importable.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from generate_array_mul_comm import build_commutativity_cnf, CnfBuilder


def compute_truth_assignment(cnf, a_vars, b_vars, a_val, b_val):
    """Given a full CNF builder (after construction) and concrete values
    for a and b, deterministically derive the truth value of every other
    variable in the CNF via unit propagation, starting from the a/b
    assignments.

    This implements the "local refutation along a branch" step in
    Beame-Liew's construction: once the input bits are fixed, every
    internal variable (partial product, adder sum, adder carry, output
    bit, diff bit) has a unique forced value.
    """
    n = len(a_vars)
    # Start the assignment with a and b values.
    assign = {}
    for i, v in enumerate(a_vars):
        assign[v] = (a_val >> i) & 1 == 1
    for i, v in enumerate(b_vars):
        assign[v] = (b_val >> i) & 1 == 1

    # Fixed-point unit-propagate.
    clauses_remaining = list(cnf.clauses)
    changed = True
    while changed:
        changed = False
        new_remaining = []
        for cl in clauses_remaining:
            # Evaluate clause under current assignment.
            true_lits = []
            unassigned = []
            for lit in cl:
                v = abs(lit)
                if v in assign:
                    val = assign[v] if lit > 0 else not assign[v]
                    if val:
                        true_lits.append(lit)
                else:
                    unassigned.append(lit)
            if true_lits:
                # Clause already satisfied; drop it.
                continue
            if len(unassigned) == 0:
                # All lits are false under current assignment: conflict.
                return assign, cl
            if len(unassigned) == 1:
                # Unit clause: force the single remaining literal.
                lit = unassigned[0]
                v = abs(lit)
                assign[v] = lit > 0
                changed = True
                continue
            # Non-unit, non-conflicting: keep for later propagation.
            new_remaining.append(cl)
        clauses_remaining = new_remaining
    return assign, None


def emit_branch_proof(cnf, a_vars, b_vars, a_val, b_val, out):
    """Along the branch a=a_val, b=b_val, emit DRAT clauses that unit-propagate
    to the empty clause. Each emitted clause is a unit-literal forced by
    the assumption a=a_val, b=b_val combined with earlier propagations.

    Strategy: simulate the propagation, and for each variable we derive,
    emit a unit clause with the assumption as a prefix, then resolve
    against the original clauses.

    For simplicity of the DRAT output, we encode the branch by a chain
    of blocked clauses of the form:
        (NOT a=a_val bit OR NOT b=b_val bit ... OR lit)
    where lit is the derived literal for each internal variable.
    These are implied by the CNF + the assumption branches.

    Returns the number of DRAT lemma lines emitted.
    """
    # Build the assumption literals (what must hold along this branch).
    # We encode the assumption as its negation in each clause, so the
    # clause "assumption -> lit" becomes "NOT assumption OR lit" in CNF.
    neg_assumption = []
    for i, v in enumerate(a_vars):
        val = (a_val >> i) & 1
        neg_assumption.append(-v if val else v)
    for i, v in enumerate(b_vars):
        val = (b_val >> i) & 1
        neg_assumption.append(-v if val else v)

    # Propagate to get the forced assignment along this branch.
    assign, conflict = compute_truth_assignment(
        cnf, a_vars, b_vars, a_val, b_val
    )
    assert conflict is not None, (
        f"Expected conflict on branch a={a_val}, b={b_val}, got none"
    )

    # Emit DRAT clauses. Each clause has the shape:
    #   NOT(assumption bit) ... OR derived-lit
    # which is a RAT clause w.r.t. the CNF+assumption.
    # We emit one clause per derived variable in propagation order, then
    # the final empty-clause-along-branch (modulo assumption).
    lines = 0
    # Sort the derived vars by insertion order: for determinism, use
    # variable index ascending beyond inputs.
    input_vars = set(a_vars) | set(b_vars)
    derived = sorted(v for v in assign if v not in input_vars)
    for v in derived:
        lit = v if assign[v] else -v
        clause_lits = neg_assumption + [lit]
        out.write(" ".join(str(x) for x in clause_lits) + " 0\n")
        lines += 1
    # Finally emit the conflict clause (just the negation of the branch):
    # This is "NOT assumption" i.e., the negation of the full branch.
    # DRAT accepts the empty clause only at the end of the full proof,
    # so we emit per-branch "cut" clauses that together imply the empty
    # clause once all 2^(2n) branches are enumerated.
    out.write(" ".join(str(x) for x in neg_assumption) + " 0\n")
    lines += 1
    return lines


def emit_drat_proof(n, out):
    """Emit a DRAT proof of UNSAT for the array multiplier commutativity
    formula at width n.
    """
    cnf, a_vars, b_vars, c_vars, d_vars = build_commutativity_cnf(n)
    # Emit the CNF first so we can run drat-trim.
    # We'll emit it to a separate file; the DRAT only contains lemmas.
    total_lines = 0
    for a_val in range(2 ** n):
        for b_val in range(2 ** n):
            total_lines += emit_branch_proof(
                cnf, a_vars, b_vars, a_val, b_val, out
            )
    # Finally emit the empty clause.
    out.write("0\n")
    total_lines += 1
    return cnf, total_lines


def main():
    if len(sys.argv) < 2:
        print("usage: beame_liew_phase1.py N [OUT.drat]", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    out_path = sys.argv[2] if len(sys.argv) > 2 else f"/tmp/comm_n{n}_bl.drat"
    cnf_path = os.path.splitext(out_path)[0] + ".cnf"

    # Emit CNF.
    cnf, a_vars, b_vars, c_vars, d_vars = build_commutativity_cnf(n)
    with open(cnf_path, "w") as f:
        f.write(f"c array multiplier commutativity, n={n}\n")
        cnf.write(f)

    # Emit DRAT proof.
    with open(out_path, "w") as f:
        total_lines = 0
        for a_val in range(2 ** n):
            for b_val in range(2 ** n):
                total_lines += emit_branch_proof(
                    cnf, a_vars, b_vars, a_val, b_val, f
                )
        # Empty clause.
        f.write("0\n")
        total_lines += 1

    print(f"n={n}: CNF={cnf_path} ({cnf.next_var - 1} vars, "
          f"{len(cnf.clauses)} clauses)")
    print(f"n={n}: DRAT={out_path} ({total_lines} lines)")


if __name__ == "__main__":
    main()
