#!/usr/bin/env python3
"""
DRAT emission for paper-exact BP (phase3_bp_paper.py).

Uses path-negation at leaves (guaranteed to be RUP against the strip
CNF since leaves are conflict nodes where propagation fails), then
post-order resolution to bubble up to the empty clause.

Every merge is tree-unfolded: we visit a merged subtree once per
incoming path. This can lead to larger DRAT than the BP, but each
visit produces a distinct path-negation clause.
"""

import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper import build_bp_paper


def emit_tree_post_order(bp, out):
    """Walk BP in post-order, emitting DRAT lemmas by path-negation
    at leaves and resolution at internal branching nodes.

    Returns the set of lemmas emitted.
    """
    nodes = bp['nodes']
    emitted = set()

    def rec(nid, path_lits):
        node = nodes[nid]
        if node.get('leaf'):
            # Path-negation: emit clause {-l : l in path_lits}.
            clause = frozenset(-l for l in path_lits)
            if clause and clause not in emitted:
                lits = sorted(clause, key=lambda x: (abs(x), x))
                out.write(' '.join(str(l) for l in lits) + ' 0\n')
                emitted.add(clause)
            elif not clause and frozenset() not in emitted:
                out.write('0\n')
                emitted.add(frozenset())
            return clause

        children = node['children']
        # Identify kind: branch or merge.
        lits = [k for k in children.keys() if isinstance(k, int)]
        if lits:
            # Branching node.
            if len(lits) != 2:
                return None
            l_pos = next((x for x in lits if x > 0), None)
            l_neg = next((x for x in lits if x < 0), None)
            if l_pos is None or l_neg is None:
                return None

            # Recurse on each branch with path extended.
            path_lits.append(l_pos)
            c_pos = rec(children[l_pos], path_lits)
            path_lits.pop()

            path_lits.append(l_neg)
            c_neg = rec(children[l_neg], path_lits)
            path_lits.pop()

            if c_pos is None or c_neg is None:
                return None
            var = abs(l_pos)
            # c_pos came from V=1 branch; its clause contains -V (= l_neg).
            # c_neg came from V=0 branch; its clause contains +V (= l_pos).
            has_neg_in_pos = l_neg in c_pos
            has_pos_in_neg = l_pos in c_neg
            if has_neg_in_pos and has_pos_in_neg:
                res = frozenset((c_pos - {l_neg}) | (c_neg - {l_pos}))
            elif l_pos in c_pos and l_neg in c_neg:
                # Reversed (rare)
                res = frozenset((c_pos - {l_pos}) | (c_neg - {l_neg}))
            else:
                # One child doesn't contain the branching var.
                if l_pos not in c_pos and l_neg not in c_pos:
                    res = c_pos  # c_pos already var-free, use as-is
                elif l_pos not in c_neg and l_neg not in c_neg:
                    res = c_neg
                else:
                    res = c_pos & c_neg

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
            # Merge: no branching at this level, just descend.
            return rec(children[('merge',)], path_lits)
        else:
            return None

    rec(0, [])
    return emitted


def emit_drat_paper(n, k, cnf_path, drat_path):
    cnf, strip_clauses, bp, role2var, out_c, out_d = build_bp_paper(n, k)

    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, 'w') as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(' '.join(str(l) for l in cl) + ' 0\n')

    with open(drat_path, 'w') as f:
        emit_tree_post_order(bp, f)


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_paper_drat.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf_path = f"/tmp/strip_paper_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_paper_n{n}_k{k}.drat"
    emit_drat_paper(n, k, cnf_path, drat_path)

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
