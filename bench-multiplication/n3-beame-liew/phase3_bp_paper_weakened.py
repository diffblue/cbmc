#!/usr/bin/env python3
"""
DAG DRAT emission with EXPLICIT WEAKENING steps for Prop 2.1.

For each internal BP node branching on V with children c0 (V=0), c1 (V=1):
1. Post-order: emit c0's clause and c1's clause first.
2. If clause(c0) doesn't contain V, emit weakening (clause(c0) ∨ V).
   - This is RUP because clause(c0) is RUP and adding V makes it weaker.
3. Similarly weaken clause(c1) with -V.
4. Emit resolvent on V = parent's clause.

Each step is RUP-valid, so the entire chain validates with drat-trim.

Leaves: emit ¬Cut-state clause (RUP because strip CNF ∧ Cut-state → ⊥
via UP from the leaf-reaching branch).
"""

import os
import subprocess
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import phase3_bp_paper
from phase3_bp_paper import build_bp_paper


def emit_weakened_dag(bp, out):
    """Emit DAG DRAT with Prop 2.1 weakening + resolution."""
    nodes = bp['nodes']
    clause_of = {}
    emitted = set()

    def emit_clause(cl):
        """Emit a clause; return True if actually emitted."""
        cl = frozenset(cl)
        if cl in emitted:
            return False
        lits = sorted(cl, key=lambda x: (abs(x), x))
        if lits:
            out.write(' '.join(str(l) for l in lits) + ' 0\n')
        else:
            out.write('0\n')
        emitted.add(cl)
        return True

    def post(nid):
        if nid in clause_of:
            return clause_of[nid]
        node = nodes[nid]

        if node.get('leaf'):
            # Leaf: emit path-negation clause (which is RUP-valid because
            # strip clauses with path assignment propagate to conflict).
            # Collect full branching path from root.
            path_lits = []
            cur = nid
            while cur is not None:
                nd = nodes[cur]
                if nd.get('branch_lit') is not None:
                    path_lits.append(nd['branch_lit'])
                cur = nd['parent']
            clause = frozenset(-l for l in path_lits)
            clause_of[nid] = clause
            emit_clause(clause)
            return clause

        children = node['children']
        lits = [k for k in children.keys() if isinstance(k, int)]
        if lits:
            if len(lits) != 2:
                return None
            l_pos = next(x for x in lits if x > 0)
            l_neg = next(x for x in lits if x < 0)
            c_pos = post(children[l_pos])
            c_neg = post(children[l_neg])
            if c_pos is None or c_neg is None:
                return None

            var = abs(l_pos)

            # Weakening step: ensure c_pos contains l_neg (= -V) if not.
            # c_pos is from V=1 branch → path-negation contains -V; but
            # if children were merged (DAG), clauses may have been modified.
            # Ensure both sides have proper polarity for resolution.
            if l_neg not in c_pos:
                weakened_pos = c_pos | {l_neg}
                emit_clause(weakened_pos)
            else:
                weakened_pos = c_pos

            if l_pos not in c_neg:
                weakened_neg = c_neg | {l_pos}
                emit_clause(weakened_neg)
            else:
                weakened_neg = c_neg

            # Resolve: (weakened_pos minus -V) ∨ (weakened_neg minus +V).
            res = frozenset(
                (weakened_pos - {l_neg}) | (weakened_neg - {l_pos})
            )
            clause_of[nid] = res
            emit_clause(res)
            return res
        elif ('merge',) in children:
            target = children[('merge',)]
            c = post(target)
            clause_of[nid] = c
            return c
        return None

    root = post(0)
    # Ensure final empty clause
    if root and root != frozenset() and frozenset() not in emitted:
        # Root's clause wasn't empty; cannot derive UNSAT via this path.
        # Emit 0 anyway and let drat-trim fail to show issue.
        out.write('0\n')
        emitted.add(frozenset())


def emit_drat_weakened(n, k, cnf_path, drat_path):
    phase3_bp_paper.MERGE_NODES = True  # DAG
    cnf, strip_clauses, bp, _, _, _ = build_bp_paper(n, k)
    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, 'w') as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(' '.join(str(l) for l in cl) + ' 0\n')
    with open(drat_path, 'w') as f:
        emit_weakened_dag(bp, f)


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_paper_weakened.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])
    cnf_path = f"/tmp/strip_paper_weak_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_paper_weak_n{n}_k{k}.drat"
    emit_drat_weakened(n, k, cnf_path, drat_path)
    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n} k={k}: CNF {cnf_bytes}B, DRAT {drat_bytes}B ({drat_lines} lemmas)")

    result = subprocess.run(
        ['/tmp/drat-trim', cnf_path, drat_path],
        capture_output=True, text=True, timeout=300,
    )
    for line in result.stdout.split('\n'):
        if line.startswith('s '):
            print(f"  {line}")


if __name__ == "__main__":
    main()
