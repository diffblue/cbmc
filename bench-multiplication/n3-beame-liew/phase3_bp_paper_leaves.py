#!/usr/bin/env python3
"""
Alternative DRAT emission: only emit leaf path-negation clauses,
plus the empty clause at the end. Let drat-trim derive intermediate
resolvents via backward checking.

This is simpler than post-order resolution and sidesteps issues with
our Python resolver. drat-trim's backward checker will reject if the
empty clause isn't derivable from leaves alone, so this is a valid
correctness test.
"""

import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper import build_bp_paper


def collect_leaf_paths(bp):
    """Traverse BP, returning list of (leaf_id, path_lits) pairs."""
    nodes = bp['nodes']
    results = []

    def rec(nid, path):
        node = nodes[nid]
        if node.get('leaf'):
            results.append((nid, list(path)))
            return
        children = node['children']
        lits = [k for k in children.keys() if isinstance(k, int)]
        if lits:
            for lit in lits:
                path.append(lit)
                rec(children[lit], path)
                path.pop()
        elif ('merge',) in children:
            rec(children[('merge',)], path)

    rec(0, [])
    return results


def emit_leaves_only(bp, out):
    """Emit path-negation for each leaf, then final empty clause."""
    emitted = set()
    for nid, path in collect_leaf_paths(bp):
        clause = frozenset(-l for l in path)
        if clause in emitted:
            continue
        emitted.add(clause)
        lits = sorted(clause, key=lambda x: (abs(x), x))
        out.write(' '.join(str(l) for l in lits) + ' 0\n')
    # Final empty clause.
    out.write('0\n')


def emit_drat_leaves(n, k, cnf_path, drat_path):
    cnf, strip_clauses, bp, _, _, _ = build_bp_paper(n, k)
    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, 'w') as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(' '.join(str(l) for l in cl) + ' 0\n')
    with open(drat_path, 'w') as f:
        emit_leaves_only(bp, f)


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_paper_leaves.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])
    cnf_path = f"/tmp/strip_paper_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_paper_leaves_n{n}_k{k}.drat"
    emit_drat_leaves(n, k, cnf_path, drat_path)

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
