#!/usr/bin/env python3
"""
N3 Phase 3 full proof using diagonal BP.
Analogous to phase3_full_cut.py but uses phase3_bp_diag.
"""

import os
import sys
import subprocess

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper_order import build_strip_all
from generate_array_mul_comm_meta import build_commutativity_cnf_meta
from phase3_bp_diag import build_bp_diag
from phase3_bp_cut_drat import emit_tree_post_order_cut


def compose_full_proof_diag(n, out_cnf, out_drat):
    cnf, _, _, _, _ = build_commutativity_cnf_meta(n)
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
        pp_c_vars = {}
        pp_d_vars = {}
        for v, role in cnf.meta.items():
            if role and role[0] == "pp_c":
                pp_c_vars[(role[1], role[2])] = v
            elif role and role[0] == "pp_d":
                pp_d_vars[(role[1], role[2])] = v
        for (i, j), cv in pp_c_vars.items():
            dv_key = (j, i)
            if dv_key in pp_d_vars:
                dv = pp_d_vars[dv_key]
                if cv == dv:
                    continue
                out.write(f"{-cv} {dv} 0\n")
                out.write(f"{cv} {-dv} 0\n")

        strip_sizes = []
        for k in range(0, 2*n):
            cnf_s, strip_clauses, forced_e, delta = build_strip_all(n, k)
            extras = set()
            for i, dv in enumerate(diff_vars):
                if i < k:
                    extras.add(dv)
                elif i == k:
                    extras.add(-dv)
            bp = build_bp_diag(n, k)

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
            if bp.get("conflict") is not None:
                ww.write("0")
            else:
                emit_tree_post_order_cut(bp, ww)
            strip_sizes.append(ww.count)

        for k in range(1, 2*n):
            out.write(f"{-diff_vars[k]} 0\n")
        out.write("0\n")

    return strip_sizes


def main():
    if len(sys.argv) != 2:
        print("usage: phase3_full_diag.py N", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    cnf_path = f"/tmp/phase3_full_diag_n{n}.cnf"
    drat_path = f"/tmp/phase3_full_diag_n{n}.drat"
    strip_sizes = compose_full_proof_diag(n, cnf_path, drat_path)
    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n}: CNF {cnf_bytes}B, DRAT {drat_bytes}B ({drat_lines} lemmas)")
    print(f"  strip sizes: {strip_sizes}")
    result = subprocess.run(
        ["/tmp/drat-trim", cnf_path, drat_path],
        capture_output=True, text=True, timeout=1200,
    )
    for line in result.stdout.split("\n"):
        if line.startswith("s "):
            print(f"  {line}")


if __name__ == "__main__":
    main()
