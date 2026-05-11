#!/usr/bin/env python3
"""
Phase 3 approach via per-strip SAT refutation.

For each k in [0, 2n-1], extract phi_Strip(k), run CaDiCaL to obtain
a DRAT refutation of the strip alone, then compose the per-strip
DRAT proofs plus the top-level case split on k into a single DRAT
refutation of the full CNF.

This is a "metered" version of Beame-Liew: instead of constructing
the BP by hand, we let the SAT solver find a refutation for each
strip. Each strip refutation is a short proof (the strip is small),
so the total is smaller than the full-formula proof.

Key question: is the SUM of per-strip DRAT proofs smaller than
the Phase 1 flat enumeration at a given n?

Usage: python3 phase3_per_strip.py N
"""

import math
import os
import sys
import subprocess
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_strip_extract import (
    build_strip_cnf,
    write_cnf,
    strip_delta,
)

CADICAL = "/home/ubuntu/cadical-src/build/cadical"
DRAT_TRIM = "/tmp/drat-trim"


def run_cadical_drat(cnf_path, drat_path):
    subprocess.run(
        [CADICAL, "--no-binary", cnf_path, drat_path],
        capture_output=True, timeout=600,
    )


def validate_drat(cnf_path, drat_path):
    result = subprocess.run(
        [DRAT_TRIM, cnf_path, drat_path],
        capture_output=True, text=True, timeout=60,
    )
    for line in result.stdout.split("\n"):
        if line.startswith("s "):
            return line.strip()
    return "?"


def main():
    if len(sys.argv) != 2:
        print("usage: phase3_per_strip.py N", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    delta = strip_delta(n)
    print(f"n={n}, Delta={delta}")

    total_strip_drat = 0
    per_strip_sizes = []
    for k in range(1, 2 * n):
        cnf, strip_clauses, used_vars, _ = build_strip_cnf(n, k)
        max_var = max(used_vars) if used_vars else 1
        with tempfile.NamedTemporaryFile(
            suffix=".cnf", delete=False
        ) as cnf_f, tempfile.NamedTemporaryFile(
            suffix=".drat", delete=False
        ) as drat_f:
            cnf_path = cnf_f.name
            drat_path = drat_f.name
        write_cnf(cnf_path, max_var, strip_clauses)
        run_cadical_drat(cnf_path, drat_path)
        status = validate_drat(cnf_path, drat_path)
        size_drat = os.path.getsize(drat_path)
        size_cnf = os.path.getsize(cnf_path)
        total_strip_drat += size_drat
        per_strip_sizes.append((k, size_cnf, size_drat, status))
        os.unlink(cnf_path)
        os.unlink(drat_path)

    print(f"{'k':>3}  {'CNF bytes':>10}  {'DRAT bytes':>10}  status")
    for k, sc, sd, status in per_strip_sizes:
        print(f"{k:>3}  {sc:>10}  {sd:>10}  {status}")
    print()
    print(f"Total per-strip DRAT: {total_strip_drat} bytes "
          f"(sum across {len(per_strip_sizes)} strips)")

    # Compare to Phase 1 and to full CNF CaDiCaL
    p1_path = f"/tmp/comm_n{n}_bl.drat"
    if os.path.exists(p1_path):
        p1_size = os.path.getsize(p1_path)
        print(f"Phase 1 DRAT: {p1_size} bytes")
        print(f"Per-strip / Phase 1: {total_strip_drat / p1_size:.2f}x")
    # Generate full CNF and measure
    full_cnf_path = f"/tmp/comm_n{n}_full.cnf"
    full_drat_path = f"/tmp/comm_n{n}_full.drat"
    with open(full_cnf_path, "w") as f:
        cnf.write(f)
    run_cadical_drat(full_cnf_path, full_drat_path)
    full_drat_size = os.path.getsize(full_drat_path)
    print(f"CaDiCaL on full CNF: {full_drat_size} bytes")
    print(f"Per-strip / CaDiCaL full: "
          f"{total_strip_drat / full_drat_size:.2f}x")


if __name__ == "__main__":
    main()
