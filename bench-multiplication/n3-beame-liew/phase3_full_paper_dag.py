#!/usr/bin/env python3
"""
Full commutativity proof using paper-true DAG DRAT emission.
Uses phase3_bp_paper_prop21_true's Prop 2.1 construction with hash consing.
"""

import io
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from generate_sym_mul_comm_meta import symmetry_substituted_cnf
from phase3_bp_paper_prop21_true import (
    PaperBP,
    compute_clauses,
)
from phase3_strip_extract import extract_strip, forced_e_assignment
from phase3_bp_paper_sym import paper_branch_vars_onesided
from fast_propagate import build_clause_index
import math


def emit_dag_weakened(bp, root_id, clause_of, cnf_set, extras, out):
    """Emit DRAT lemmas in topological order, weakening with `extras`.

    extras: set of literals to add (OR) to each lemma.
    cnf_set: set of frozensets of CNF clauses (skip these).
    """
    emitted = set()

    def visit(nid):
        if nid in emitted:
            return
        emitted.add(nid)
        node = bp.nodes[nid]
        if node['kind'] == 'branch':
            visit(node['c0'])
            visit(node['c1'])
        if node['kind'] == 'leaf_conflict':
            return  # CNF axiom
        cl = clause_of[nid]
        weakened = frozenset(cl) | extras
        if weakened in cnf_set:
            return
        lits = sorted(weakened, key=lambda x: (abs(x), x))
        if lits:
            out.write(' '.join(str(l) for l in lits) + ' 0\n')
        else:
            out.write('0\n')

    visit(root_id)


def build_and_emit_strip(n, k, extras, out_f, cnf_set):
    """Build DAG BP for a strip at (n, k), emit DRAT (weakened by extras)."""
    cnf, a, b, c_bits, d_bits = symmetry_substituted_cnf(n)
    delta = max(1, math.ceil(math.log2(max(2 * n, 2))))
    strip_clauses = extract_strip(cnf, k, delta)
    forced_e_units = forced_e_assignment(cnf, k, n)
    strip_clauses = strip_clauses + forced_e_units
    clauses = [list(cl) for cl in strip_clauses]
    var_index = build_clause_index(clauses)

    role2var = {}
    for v, role in cnf.meta.items():
        role2var[role] = v

    initial_sigma = {}
    for cl in forced_e_units:
        if len(cl) == 1:
            lit = cl[0]
            initial_sigma[abs(lit)] = lit > 0

    bp = PaperBP(clauses, var_index)

    # Concatenate branching vars across all levels.
    all_branch_vars = []
    for j in range(0, k + 1):
        bv = paper_branch_vars_onesided(j, k, delta, n, role2var)
        for v in bv:
            if v not in all_branch_vars:
                all_branch_vars.append(v)

    root_id = bp.build_node(
        initial_sigma, all_branch_vars, cut_vars=set(), use_cache=False
    )
    clause_of = compute_clauses(bp.nodes)
    emit_dag_weakened(bp, root_id, clause_of, cnf_set, extras, out_f)
    return len(bp.nodes)


def compose_full_proof(n, out_cnf, out_drat):
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

    cnf_set = set(frozenset(cl) for cl in all_clauses)

    bp_sizes = []
    with open(out_drat, "w") as out:
        for k in range(0, 2 * n):
            extras = set()
            for i, dv in enumerate(diff_vars):
                if i < k:
                    extras.add(dv)
                elif i == k:
                    extras.add(-dv)
            size = build_and_emit_strip(n, k, extras, out, cnf_set)
            bp_sizes.append(size)

        for k in range(1, 2 * n):
            out.write(f"{-diff_vars[k]} 0\n")
        out.write("0\n")

    return bp_sizes


def main():
    if len(sys.argv) != 2:
        print("usage: phase3_full_paper_dag.py N", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    cnf_path = f"/tmp/phase3_full_dag_n{n}.cnf"
    drat_path = f"/tmp/phase3_full_dag_n{n}.drat"
    bp_sizes = compose_full_proof(n, cnf_path, drat_path)
    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n}: CNF {cnf_bytes}B, DRAT {drat_bytes}B ({drat_lines} lemmas)")
    print(f"  BP sizes: {bp_sizes}")
    result = subprocess.run(
        ["/tmp/drat-trim", cnf_path, drat_path],
        capture_output=True, text=True, timeout=1800,
    )
    for line in result.stdout.split("\n"):
        if line.startswith("s "):
            print(f"  {line}")


if __name__ == "__main__":
    main()
