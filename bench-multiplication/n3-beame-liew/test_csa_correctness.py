#!/usr/bin/env python3
"""
Verify CSA multiplier computes a*b correctly by:
1. Setting a, b to specific values.
2. Solving the CNF with the solver.
3. Reading out the output bits.
4. Comparing to a*b.

Runs for all (a, b) in [0, 2^n) for small n.
"""

import os
import sys
import subprocess
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from generate_csa_mul_comm_meta import CsaBuilder


def test_csa(n, a_val, b_val):
    """Test that CSA multiplier with a=a_val, b=b_val gives a*b."""
    cnf = CsaBuilder()
    a = [cnf.new_var(("a_bit", i)) for i in range(n)]
    b = [cnf.new_var(("b_bit", i)) for i in range(n)]
    c = cnf.csa_multiplier(a, b, side="c")

    # Force a, b values
    for i in range(n):
        if (a_val >> i) & 1:
            cnf.add_clause([a[i]])
        else:
            cnf.add_clause([-a[i]])
        if (b_val >> i) & 1:
            cnf.add_clause([b[i]])
        else:
            cnf.add_clause([-b[i]])

    with tempfile.NamedTemporaryFile(mode='w', suffix='.cnf', delete=False) as f:
        cnf_path = f.name
        f.write(f"p cnf {cnf.next_var - 1} {len(cnf.clauses)}\n")
        for cl in cnf.clauses:
            f.write(" ".join(str(l) for l in cl) + " 0\n")

    out_path = cnf_path + ".out"
    # Run minisat / cadical to find assignment
    result = subprocess.run(
        ["minisat", cnf_path, out_path],
        capture_output=True, text=True, timeout=30,
    )
    os.unlink(cnf_path)

    # Parse assignment from output file
    assign = {}
    try:
        with open(out_path) as f:
            content = f.read()
        os.unlink(out_path)
    except FileNotFoundError:
        content = ""
    if "UNSAT" in content:
        return None
    for line in content.split("\n"):
        line = line.strip()
        if line in ("SAT", "UNSAT", ""):
            continue
        for tok in line.split():
            try:
                lit = int(tok)
            except ValueError:
                continue
            if lit == 0:
                break
            assign[abs(lit)] = lit > 0

    if not assign:
        return None

    # Read c bits
    c_val = 0
    for i, cv in enumerate(c):
        if assign.get(cv, False):
            c_val |= (1 << i)
    return c_val


def main():
    for n in [3, 4, 5]:
        print(f"=== n={n} ===")
        errors = 0
        for a_val in range(1 << n):
            for b_val in range(1 << n):
                expected = (a_val * b_val) & ((1 << (2 * n)) - 1)
                actual = test_csa(n, a_val, b_val)
                if actual != expected:
                    print(f"  a={a_val} b={b_val}: expected {expected}, got {actual}")
                    errors += 1
        if errors == 0:
            print(f"  All {4 ** n} combinations correct.")
        else:
            print(f"  {errors} errors found.")


if __name__ == "__main__":
    main()
