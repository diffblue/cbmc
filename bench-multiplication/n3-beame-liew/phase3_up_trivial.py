#!/usr/bin/env python3
"""
Check which phi_Strip(k) UP-refute from the forced e assignment
alone (no input branching needed). For those strips the BP is
trivial: a single UP derivation that emits the conflict clause as
the empty clause.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_build import (
    build_strip_with_e_forced,
    propagate_full,
)


def main():
    if len(sys.argv) != 2:
        print("usage: phase3_up_trivial.py N", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    print(f"n={n}: which strips are UP-refutable from forced e alone?")
    for k in range(1, 2 * n):
        cnf, strip_clauses, e_assign, delta = build_strip_with_e_forced(n, k)
        forced_e = {}
        for cl in e_assign:
            forced_e[abs(cl[0])] = cl[0] > 0
        full_clauses = strip_clauses + e_assign
        final, conflict = propagate_full(full_clauses, forced_e)
        if conflict is None:
            print(f"  k={k:2d}: UP-trivial? NO (need branching)")
        else:
            print(f"  k={k:2d}: UP-trivial? YES (conflict on clause {conflict})")


if __name__ == "__main__":
    main()
