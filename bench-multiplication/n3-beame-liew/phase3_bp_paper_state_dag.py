#!/usr/bin/env python3
"""
State-based DAG DRAT emission for paper BP.

For each BP node, emit a clause that is the NEGATION OF THE CUT STATE
at that node. Paper's Prop 2.1 claims this clause is RUP-valid:

- For leaves: CNF ∧ state(leaf) is UNSAT (by construction: UP derived
  conflict when reaching this leaf). So ¬state(leaf) is RUP.
- For internal nodes branching on V: ¬state(parent) = resolve(
    ¬state(c_pos), ¬state(c_neg), V). Resolvent is RUP given children.
- For merges: parent-node clause = child-node clause (same state).
  No emission needed.

Emission order: post-order over the BP DAG.
"""

import os
import subprocess
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import phase3_bp_paper
from phase3_bp_paper import build_bp_paper


def state_to_clause(state):
    """Convert state tuple [(var, val), ...] to negation clause."""
    lits = []
    for v, val in state:
        lits.append(-v if val else v)
    return frozenset(lits)


def emit_state_dag(bp, out):
    """Emit ¬state at each BP node, in post-order."""
    nodes = bp['nodes']
    clause_of = {}
    emitted = set()

    def cluster_state(nid):
        """Returns the full branching path + cut state as clause.

        For a leaf node, clause = path-negation.
        For an internal node after resolution, the clause should
        accumulate the UP-derived state.
        """
        node = nodes[nid]
        # Collect branching path from root.
        path_lits = []
        cur = nid
        while cur is not None:
            nd = nodes[cur]
            if nd.get('branch_lit') is not None:
                path_lits.append(nd['branch_lit'])
            cur = nd['parent']
        return frozenset(-l for l in path_lits)

    def post(nid):
        if nid in clause_of:
            return clause_of[nid]

        node = nodes[nid]
        if node.get('leaf'):
            # Use path-negation.
            clause = cluster_state(nid)
            clause_of[nid] = clause
            if clause and clause not in emitted:
                lits = sorted(clause, key=lambda x: (abs(x), x))
                out.write(' '.join(str(l) for l in lits) + ' 0\n')
                emitted.add(clause)
            elif not clause and frozenset() not in emitted:
                out.write('0\n')
                emitted.add(frozenset())
            return clause

        children = node['children']
        lits = [k for k in children.keys() if isinstance(k, int)]
        if lits:
            # Branching node: post-order on children.
            if len(lits) != 2:
                return None
            l_pos = next(x for x in lits if x > 0)
            l_neg = next(x for x in lits if x < 0)
            c_pos = post(children[l_pos])
            c_neg = post(children[l_neg])
            if c_pos is None or c_neg is None:
                return None

            var = abs(l_pos)
            # c_pos came from V=1 branch; should contain -V.
            # c_neg came from V=0 branch; should contain +V.
            if l_neg in c_pos and l_pos in c_neg:
                res = frozenset((c_pos - {l_neg}) | (c_neg - {l_pos}))
            elif l_neg in c_pos:
                res = c_pos - {l_neg}
            elif l_pos in c_neg:
                res = c_neg - {l_pos}
            else:
                # Neither has the branching var.
                res = c_pos & c_neg

            clause_of[nid] = res
            if res != c_pos and res != c_neg and res not in emitted:
                if res:
                    slits = sorted(res, key=lambda x: (abs(x), x))
                    out.write(' '.join(str(l) for l in slits) + ' 0\n')
                    emitted.add(res)
                elif frozenset() not in emitted:
                    out.write('0\n')
                    emitted.add(frozenset())
            return res
        elif ('merge',) in children:
            target = children[('merge',)]
            c = post(target)
            clause_of[nid] = c
            return c
        return None

    root = post(0)
    # Ensure final empty clause
    if root != frozenset():
        # Attempt to produce empty via additional resolution steps
        # (this indicates BP root's clause wasn't empty).
        pass
    if frozenset() not in emitted:
        out.write('0\n')


def emit_drat_state(n, k, cnf_path, drat_path):
    phase3_bp_paper.MERGE_NODES = True  # DAG
    phase3_bp_paper.USE_AUGMENTED_CUT = True  # sufficient cut for state refute
    cnf, strip_clauses, bp, _, _, _ = build_bp_paper(n, k)
    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, 'w') as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(' '.join(str(l) for l in cl) + ' 0\n')
    with open(drat_path, 'w') as f:
        emit_state_dag(bp, f)


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_paper_state_dag.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])
    cnf_path = f"/tmp/strip_paper_state_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_paper_state_n{n}_k{k}.drat"
    emit_drat_state(n, k, cnf_path, drat_path)
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
