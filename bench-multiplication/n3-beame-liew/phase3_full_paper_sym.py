#!/usr/bin/env python3
"""
Full commutativity proof using sym-substituted tree BP.

Analogous to phase3_full_paper.py but uses sym CNF, which eliminates
pp_d vars via symmetry substitution.
"""

import os
import sys
import subprocess

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import phase3_bp_paper_sym
from phase3_bp_paper_sym import build_bp_paper_sym
from generate_sym_mul_comm_meta import symmetry_substituted_cnf
from phase3_bp_paper_sym_tree import emit_tree_post_order


def compose_full_proof_sym(n, out_cnf, out_drat):
    phase3_bp_paper_sym.MERGE_NODES = False  # Tree mode for valid DRAT

    cnf, a, b, c_bits, d_bits = symmetry_substituted_cnf(n)
    all_clauses = list(cnf.clauses)

    diff_vars = sorted(
        [v for v, r in cnf.meta.items() if r and r[0] == "diff"],
        key=lambda v: cnf.meta[v][1]
    )
    max_var = cnf.next_var - 1
    with open(out_cnf, "w") as f:
        f.write(f"p cnf {max_var} {len(all_clauses)}\n")
        for cl in all_clauses:
            f.write(" ".join(str(l) for l in cl) + " 0\n")

    with open(out_drat, "w") as out:
        strip_sizes = []
        for k in range(0, 2*n):
            _, strip_clauses, bp, _, _, _ = build_bp_paper_sym(n, k)

            extras = set()
            for i, dv in enumerate(diff_vars):
                if i < k:
                    extras.add(dv)
                elif i == k:
                    extras.add(-dv)

            class WeakenedWriter:
                def __init__(self, f, extras):
                    self.f = f
                    self.extras = extras
                    self.count = 0

                def write(self, s):
                    for line in s.split("\n"):
                        line = line.strip()
                        if not line:
                            continue
                        lits = [int(x) for x in line.split()][:-1]
                        weakened = frozenset(lits) | self.extras
                        sorted_lits = sorted(weakened, key=lambda x: (abs(x), x))
                        if sorted_lits:
                            self.f.write(" ".join(str(l) for l in sorted_lits) + " 0\n")
                        else:
                            self.f.write("0\n")
                        self.count += 1

            ww = WeakenedWriter(out, extras)
            emit_tree_post_order(bp, ww)
            strip_sizes.append(ww.count)

        for k in range(1, 2*n):
            out.write(f"{-diff_vars[k]} 0\n")
        out.write("0\n")

    return strip_sizes


def main():
    if len(sys.argv) != 2:
        print("usage: phase3_full_paper_sym.py N", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    cnf_path = f"/tmp/phase3_full_sym_n{n}.cnf"
    drat_path = f"/tmp/phase3_full_sym_n{n}.drat"
    strip_sizes = compose_full_proof_sym(n, cnf_path, drat_path)
    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n}: CNF {cnf_bytes}B, DRAT {drat_bytes}B ({drat_lines} lemmas)")
    print(f"  strip sizes: {strip_sizes}")
    result = subprocess.run(
        ["/tmp/drat-trim", cnf_path, drat_path],
        capture_output=True, text=True, timeout=1800,
    )
    for line in result.stdout.split("\n"):
        if line.startswith("s "):
            print(f"  {line}")


if __name__ == "__main__":
    main()
