#!/usr/bin/env python3
"""
Phase 3 step 1: extract the critical-strip formula phi_Strip(k) from the
full array-multiplier commutativity CNF (Beame-Liew 2017 §3.3).

phi_Strip(k) consists of:
  (a) all clauses from the CNF that contain any tableau variable
      pp_c[i][j] or pp_d[i][j] with i+j in [k-Delta, k]
      (Delta = ceil(log2(2n)));
  (b) the forced assignment e_0=0, e_1=0, ..., e_{k-1}=0, e_k=1
      (unit clauses).

Lemma 3.1 (Beame-Liew): phi_Strip(k) is UNSAT for all k.

This script extracts phi_Strip(k), writes it to DIMACS, and runs a
SAT solver to confirm UNSAT -- a prerequisite for the Phase 3 BP
construction.

Usage: python3 phase3_strip_extract.py N K
"""

import math
import os
import sys
import subprocess

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from generate_array_mul_comm_meta import build_commutativity_cnf_meta


def strip_delta(n):
    # The paper uses Delta = log n (natural log or log_2?). For a 2n-bit
    # output, log_2(2n) is the natural choice. We use ceil for safety
    # (the strip is only required to be "wide enough" per Lemma 3.1).
    return math.ceil(math.log2(max(2 * n, 2)))


def is_tableau_var(meta_role):
    if meta_role is None:
        return False
    return meta_role[0] in ("pp_c", "pp_d")


def tableau_col(meta_role):
    """For a tableau role ("pp_{c|d}", i, j), return the column i+j."""
    if not is_tableau_var(meta_role):
        return None
    return meta_role[1] + meta_role[2]


def var_col(meta_role):
    """Return the column index (i+j or col) for any column-associated
    variable role. Returns None for inputs/zero/etc. whose column is
    not well-defined.
    """
    if meta_role is None:
        return None
    tag = meta_role[0]
    if tag in ("pp_c", "pp_d"):
        return meta_role[1] + meta_role[2]
    if tag in ("acc_c", "acc_d", "cry_c", "cry_d"):
        # role = (tag, row, col)
        return meta_role[2]
    if tag == "diff":
        return meta_role[1]
    return None


def extract_strip(cnf, k, delta):
    """Return the list of clauses constituting phi_Strip(k).

    Clauses in the strip:
      1. Any clause containing a variable whose column is in
         [k-delta, k]. Column-carrying variables include
         tableau (pp_*), accumulator sum bits (acc_*), carry bits
         (cry_*), and diff. We deliberately include carries and
         accumulators so the strip's adder chain is self-contained.
      2. Tableau symmetry clauses pp_c[i][j] = pp_d[j][i] (following
         from AND definitions; preprocessing step in the paper).
      3. Unit clauses for the ZERO constants. Without these the
         carry-chain starts from an unconstrained value and the
         strip becomes trivially SAT.
    """
    strip_clauses = []
    included = set()
    # (1) Column-based extraction.
    for idx, cl in enumerate(cnf.clauses):
        for lit in cl:
            v = abs(lit)
            role = cnf.meta.get(v)
            col = var_col(role)
            if col is not None and k - delta <= col <= k:
                strip_clauses.append(list(cl))
                included.add(idx)
                break

    # (2) Tableau symmetry.
    pp_c = {}
    pp_d = {}
    for v, role in cnf.meta.items():
        if role is None:
            continue
        if role[0] == "pp_c":
            pp_c[(role[1], role[2])] = v
        elif role[0] == "pp_d":
            pp_d[(role[1], role[2])] = v
    for (i, j), c_var in pp_c.items():
        if k - delta <= i + j <= k:
            d_var = pp_d.get((j, i))
            if d_var is not None:
                strip_clauses.append([-c_var, d_var])
                strip_clauses.append([c_var, -d_var])

    # (3) ZERO constants (unit clauses asserting their value is 0).
    zero_vars = [v for v, role in cnf.meta.items()
                 if role and role[0] == "zero"]
    for z in zero_vars:
        strip_clauses.append([-z])

    return strip_clauses


def forced_e_assignment(cnf, k, n):
    """Return unit clauses encoding e_0=0, ..., e_{k-1}=0, e_k=1.

    In our CNF these are the diff[i] variables.
    """
    units = []
    for i, role in cnf.meta.items():
        if role and role[0] == "diff":
            bit = role[1]
            if bit < k:
                units.append([-i])   # diff[i] = 0
            elif bit == k:
                units.append([i])    # diff[k] = 1
            # bits > k are unconstrained
    return units


def build_strip_cnf(n, k):
    cnf, a_vars, b_vars, c_vars, d_vars = build_commutativity_cnf_meta(n)
    delta = strip_delta(n)
    strip_clauses = extract_strip(cnf, k, delta)
    strip_clauses += forced_e_assignment(cnf, k, n)
    # Variables: we use all vars in the strip's clauses.
    used_vars = set()
    for cl in strip_clauses:
        for lit in cl:
            used_vars.add(abs(lit))
    # For DIMACS "p cnf V C", V can be >= max var. Use the CNF's global
    # numbering directly to preserve meaning.
    return cnf, strip_clauses, used_vars, delta


def write_cnf(path, num_vars, clauses):
    with open(path, "w") as f:
        f.write(f"p cnf {num_vars} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(str(x) for x in cl) + " 0\n")


def solve(cnf_path, solver="/home/ubuntu/cadical-src/build/cadical"):
    result = subprocess.run(
        [solver, cnf_path],
        capture_output=True, text=True, timeout=60,
    )
    out = result.stdout
    if "s UNSATISFIABLE" in out:
        return "UNSAT"
    if "s SATISFIABLE" in out:
        return "SAT"
    return "?"


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_strip_extract.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf, strip_clauses, used_vars, delta = build_strip_cnf(n, k)
    max_var = max(used_vars) if used_vars else 1

    print(f"n={n}, k={k}, Delta=log2(2n)={delta}")
    print(f"Strip columns: [{k-delta}, {k}]")
    print(f"Full CNF: {cnf.next_var - 1} vars, {len(cnf.clauses)} clauses")
    print(f"Strip:    {len(used_vars)} vars (max var = {max_var}), "
          f"{len(strip_clauses)} clauses")

    cnf_path = f"/tmp/strip_n{n}_k{k}.cnf"
    write_cnf(cnf_path, max_var, strip_clauses)

    result = solve(cnf_path)
    print(f"Strip SAT result: {result}")
    if result != "UNSAT":
        print("ERROR: strip should be UNSAT by Lemma 3.1; bug in "
              "extraction or in the CNF encoding.")
        sys.exit(1)


if __name__ == "__main__":
    main()
