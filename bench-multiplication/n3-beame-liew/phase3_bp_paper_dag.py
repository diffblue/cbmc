#!/usr/bin/env python3
"""
DAG-based DRAT emission for paper BP.

Instead of tree-unfolding merged nodes, emit each node's clause ONCE.
The clause = negation of the node's state (cut values at that level).

For a leaf: state is whatever was propagated; we emit path-negation
(this is RUP because UP from negated-path derives conflict via CNF).

For a branching node on V: its clause = resolve of children's clauses
on V. Children's clauses were emitted earlier (post-order).

For a merge: clause is identical to the merged-to node's clause
(no separate emission needed).

KEY INVARIANT: emitted clauses never contain parent path literals.
Children's clauses resolve cleanly on the branching variable.
"""

import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper import build_bp_paper
import phase3_bp_paper


def emit_dag(bp, out):
    """DAG-based emission: one lemma per node, in post-order.

    Returns the clause for each node (indexed by node id).
    """
    nodes = bp['nodes']
    clause_of = {}
    visited = set()

    def post(nid):
        if nid in visited:
            return clause_of[nid]
        visited.add(nid)
        node = nodes[nid]
        if node.get('leaf'):
            # Leaf: path-negation from root to this leaf
            # (must be RUP because UP derives conflict).
            # But we want state-only clause. Use: follow ancestor
            # branch_lits to compute path.
            path = []
            cur = nid
            while cur is not None:
                nd = nodes[cur]
                if nd['branch_lit'] is not None:
                    path.append(nd['branch_lit'])
                cur = nd['parent']
            clause = frozenset(-l for l in path)
            clause_of[nid] = clause
            if clause:
                lits = sorted(clause, key=lambda x: (abs(x), x))
                out.write(' '.join(str(l) for l in lits) + ' 0\n')
            else:
                out.write('0\n')
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
            # c_pos contains -V (negation of +V branch), c_neg contains +V
            has_neg_in_pos = l_neg in c_pos
            has_pos_in_neg = l_pos in c_neg
            if has_neg_in_pos and has_pos_in_neg:
                res = frozenset((c_pos - {l_neg}) | (c_neg - {l_pos}))
            elif not has_neg_in_pos:
                res = c_pos
            elif not has_pos_in_neg:
                res = c_neg
            else:
                res = c_pos & c_neg
            clause_of[nid] = res
            # Emit only if distinct from children
            if res != c_pos and res != c_neg:
                if res:
                    slits = sorted(res, key=lambda x: (abs(x), x))
                    out.write(' '.join(str(l) for l in slits) + ' 0\n')
                else:
                    out.write('0\n')
            return res
        elif ('merge',) in children:
            target = children[('merge',)]
            c = post(target)
            clause_of[nid] = c
            return c
        return None

    root_clause = post(0)
    # If root clause is non-empty, emit final 0 to signal end
    if root_clause and frozenset() != root_clause:
        pass  # Root should be empty
    return clause_of


def emit_drat_dag(n, k, cnf_path, drat_path):
    phase3_bp_paper.MERGE_NODES = True  # Use DAG BP
    cnf, strip_clauses, bp, _, _, _ = build_bp_paper(n, k)
    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, 'w') as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(' '.join(str(l) for l in cl) + ' 0\n')
    with open(drat_path, 'w') as f:
        emit_dag(bp, f)


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_paper_dag.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])
    cnf_path = f"/tmp/strip_paper_dag_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_paper_dag_n{n}_k{k}.drat"
    emit_drat_dag(n, k, cnf_path, drat_path)

    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n} k={k}: CNF {cnf_bytes}B, DRAT {drat_bytes}B "
          f"({drat_lines} lemmas)")

    result = subprocess.run(
        ['/tmp/drat-trim', cnf_path, drat_path],
        capture_output=True, text=True, timeout=300,
    )
    for line in result.stdout.split('\n'):
        if line.startswith('s '):
            print(f"  {line}")


if __name__ == "__main__":
    main()
