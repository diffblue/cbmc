#!/usr/bin/env python3
"""
Paper Prop 2.1 emission on sym-substituted BP DAG.

Strategy:
- At each leaf: clause = violated CNF clause (in the strip).
- At each internal BP node branching on V: clause = resolve(c0, c1, V)
  if V ∈ c0 and ¬V ∈ c1 (or vice versa). Else fall back to a child's
  clause that doesn't contain V.
- At a merge: just use target's clause.

Each clause is emitted ONCE per DAG node (not per path).

Size: O(|DAG nodes| × max_clause_size) ≈ polynomial per paper.
"""

import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import phase3_bp_paper_sym
from phase3_bp_paper_sym import build_bp_paper_sym


def emit_dag_prop21(bp, out):
    nodes = bp['nodes']
    clause_of = {}
    emitted = set()

    def emit_clause(cl):
        cl = frozenset(cl)
        if cl in emitted:
            return
        lits = sorted(cl, key=lambda x: (abs(x), x))
        if lits:
            out.write(' '.join(str(l) for l in lits) + ' 0\n')
        else:
            out.write('0\n')
        emitted.add(cl)

    def post(nid):
        if nid in clause_of:
            return clause_of[nid]
        node = nodes[nid]

        if node.get('leaf'):
            # Use violated CNF clause.
            violated = node.get('violated')
            if violated is None:
                clause_of[nid] = None
                return None
            cl = frozenset(violated)
            clause_of[nid] = cl
            # Violated clause is already in CNF, no need to emit.
            return cl

        children = node.get('children', {})
        lits = [k for k in children.keys() if isinstance(k, int)]

        if lits:
            if len(lits) != 2:
                clause_of[nid] = None
                return None
            l_pos = next((x for x in lits if x > 0), None)
            l_neg = next((x for x in lits if x < 0), None)
            if l_pos is None or l_neg is None:
                clause_of[nid] = None
                return None

            c_pos = post(children[l_pos])
            c_neg = post(children[l_neg])
            if c_pos is None or c_neg is None:
                clause_of[nid] = c_pos or c_neg
                return clause_of[nid]

            var = abs(l_pos)

            # Resolve on var if possible.
            c_pos_has_var = var in c_pos
            c_pos_has_neg = -var in c_pos
            c_neg_has_var = var in c_neg
            c_neg_has_neg = -var in c_neg

            if c_pos_has_neg and c_neg_has_var:
                res = frozenset(
                    (c_pos - {-var}) | (c_neg - {var})
                )
                emit_clause(res)
                clause_of[nid] = res
                return res
            elif c_pos_has_var and c_neg_has_neg:
                # Unusual, but resolve
                res = frozenset(
                    (c_pos - {var}) | (c_neg - {-var})
                )
                emit_clause(res)
                clause_of[nid] = res
                return res
            elif not c_pos_has_var and not c_pos_has_neg:
                # c_pos doesn't mention var; use it directly.
                clause_of[nid] = c_pos
                return c_pos
            elif not c_neg_has_var and not c_neg_has_neg:
                clause_of[nid] = c_neg
                return c_neg
            else:
                # Same polarity; use intersection.
                res = frozenset(c_pos & c_neg)
                emit_clause(res)
                clause_of[nid] = res
                return res
        elif ('merge',) in children:
            target = children[('merge',)]
            c = post(target)
            clause_of[nid] = c
            return c

        clause_of[nid] = None
        return None

    root = post(0)
    if root != frozenset():
        # Root should be empty for UNSAT
        if frozenset() not in emitted:
            out.write('0\n')
            emitted.add(frozenset())


def emit_drat_prop21(n, k, cnf_path, drat_path):
    phase3_bp_paper_sym.MERGE_NODES = True
    cnf, strip_clauses, bp, _, _, _ = build_bp_paper_sym(n, k)
    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, 'w') as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(' '.join(str(l) for l in cl) + ' 0\n')
    with open(drat_path, 'w') as f:
        emit_dag_prop21(bp, f)
    return len(bp['nodes'])


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_paper_prop21.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])
    cnf_path = f"/tmp/strip_sym_prop21_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_sym_prop21_n{n}_k{k}.drat"
    bp_size = emit_drat_prop21(n, k, cnf_path, drat_path)

    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n} k={k}: BP DAG {bp_size} nodes, "
          f"CNF {cnf_bytes}B, DRAT {drat_bytes}B ({drat_lines} lemmas)")

    result = subprocess.run(
        ['/tmp/drat-trim', cnf_path, drat_path],
        capture_output=True, text=True, timeout=300,
    )
    for line in result.stdout.split('\n'):
        if line.startswith('s '):
            print(f"  {line}")


if __name__ == "__main__":
    main()
