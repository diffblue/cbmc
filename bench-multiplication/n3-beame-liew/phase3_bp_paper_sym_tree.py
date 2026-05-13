#!/usr/bin/env python3
"""
Tree-mode DRAT emission on symmetry-substituted paper BP.

Uses path-negation clauses at leaves (RUP-valid) and post-order
resolution to build up to the empty clause at root.

Expected size: smaller than non-sym tree BP because pp_d vars are
eliminated, reducing branching factor. Should validate.
"""

import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import phase3_bp_paper_sym
from phase3_bp_paper_sym import build_bp_paper_sym


def emit_tree_post_order(bp, out):
    nodes = bp['nodes']
    emitted = set()

    def rec(nid, path_lits):
        node = nodes[nid]
        if node.get('leaf'):
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
        lits = [k for k in children.keys() if isinstance(k, int)]
        if lits:
            if len(lits) != 2:
                return None
            l_pos = next((x for x in lits if x > 0), None)
            l_neg = next((x for x in lits if x < 0), None)
            if l_pos is None or l_neg is None:
                return None

            path_lits.append(l_pos)
            c_pos = rec(children[l_pos], path_lits)
            path_lits.pop()

            path_lits.append(l_neg)
            c_neg = rec(children[l_neg], path_lits)
            path_lits.pop()

            if c_pos is None or c_neg is None:
                return None

            has_neg_in_pos = l_neg in c_pos
            has_pos_in_neg = l_pos in c_neg
            if has_neg_in_pos and has_pos_in_neg:
                res = frozenset((c_pos - {l_neg}) | (c_neg - {l_pos}))
            elif l_pos in c_pos and l_neg in c_neg:
                res = frozenset((c_pos - {l_pos}) | (c_neg - {l_neg}))
            else:
                if l_pos not in c_pos and l_neg not in c_pos:
                    res = c_pos
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
            # In tree mode, merges shouldn't happen, but handle anyway.
            return rec(children[('merge',)], path_lits)
        return None

    rec(0, [])


def emit_drat_sym_tree(n, k, cnf_path, drat_path):
    phase3_bp_paper_sym.MERGE_NODES = False  # Tree mode
    cnf, strip_clauses, bp, _, _, _ = build_bp_paper_sym(n, k)
    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, 'w') as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(' '.join(str(l) for l in cl) + ' 0\n')
    with open(drat_path, 'w') as f:
        emit_tree_post_order(bp, f)
    return len(bp['nodes'])


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_paper_sym_tree.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])
    cnf_path = f"/tmp/strip_sym_tree_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_sym_tree_n{n}_k{k}.drat"
    bp_size = emit_drat_sym_tree(n, k, cnf_path, drat_path)

    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n} k={k}: sym TREE BP {bp_size} nodes, "
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
