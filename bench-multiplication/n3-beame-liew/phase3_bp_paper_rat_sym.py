#!/usr/bin/env python3
"""
RAT extension-variable DAG DRAT emission on SYM BP.

Same strategy as phase3_bp_paper_rat.py, but:
- Uses sym-substituted CNF (smaller, no pp_d).
- Uses phase3_bp_paper_sym's BP (paper's one-sided cut, true DAG).
- Per-leaf augmentation: for each leaf, emit state-to-e clauses for
  BOTH state vars AND the path branching vars.  This guarantees
  UP-refutation at each leaf.
"""

import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import phase3_bp_paper_sym
from phase3_bp_paper_sym import build_bp_paper_sym


def topo_postorder(nodes, root_id=0):
    order = []
    visited = set()

    def visit(nid):
        if nid in visited:
            return
        visited.add(nid)
        node = nodes[nid]
        if not node.get('leaf'):
            for k, child_id in node.get('children', {}).items():
                visit(child_id)
        order.append(nid)

    visit(root_id)
    return order


def collect_paths_to_leaves(bp):
    """For each leaf, collect ALL distinct paths (branch_lit sequences)
    that reach it from the root. Returns dict leaf_id → list of paths.

    For a DAG, this can have multiple paths per leaf.
    """
    nodes = bp['nodes']
    paths_per_leaf = {}

    def dfs(nid, current_path):
        node = nodes[nid]
        if node.get('leaf'):
            paths_per_leaf.setdefault(nid, []).append(list(current_path))
            return
        children = node.get('children', {})
        for k, child_id in children.items():
            if isinstance(k, int):
                current_path.append(k)
                dfs(child_id, current_path)
                current_path.pop()
            else:
                dfs(child_id, current_path)

    dfs(0, [])
    return paths_per_leaf


def emit_rat_dag_sym(bp, out, max_cnf_var):
    """RAT emission for sym DAG BP.

    Strategy:
    1. Assign fresh extension var e_v for each DAG node.
    2. Emit {e_root} unit (RAT).
    3. For each DAG node in post-order:
       a. For LEAVES: emit state-to-e + path-to-e clauses.
          Then emit ¬e_v (RUP via UP chain: e_v → state + path → conflict).
       b. For INTERNAL nodes: emit transition clauses (RAT with fresh child-pivot).
    4. For each internal node, derive ¬e_v via resolution on children's ¬e_v.
    5. Final empty clause.
    """
    nodes = bp['nodes']
    order = topo_postorder(nodes, 0)

    # Assign fresh extension vars
    e_var = {}
    next_var = max_cnf_var + 1
    for nid in order:
        e_var[nid] = next_var
        next_var += 1

    # For leaves, compute the union of branch-lits across all paths
    paths_per_leaf = collect_paths_to_leaves(bp)

    count = [0]

    def emit(lits):
        lits = sorted(set(lits), key=lambda x: (abs(x), x))
        if lits:
            out.write(' '.join(str(l) for l in lits) + ' 0\n')
        else:
            out.write('0\n')
        count[0] += 1

    # Step 1: Emit {e_root} unit (RAT on fresh e_root pivot).
    emit([e_var[0]])

    # Step 2: Post-order traversal emitting state-to-e / transitions.
    for nid in order:
        node = nodes[nid]
        ev = e_var[nid]

        # State-to-e: ¬e_v ∨ ℓ_i for each cut state literal.
        state = node.get('state') or ()
        for (sv, sval) in state:
            state_lit = sv if sval else -sv
            emit([-ev, state_lit])

        if node.get('leaf'):
            # Per-path augmentation: for each path reaching this leaf,
            # emit ¬e_v ∨ (path_lit) for each branching literal on path.
            # Multiple paths give multiple clause sets.
            paths = paths_per_leaf.get(nid, [])
            # Emit ALL path-lits union (each as a separate implication).
            # Actually we want: e_v ∧ (path taken) → ... but for RUP to
            # give ¬e_v, we need: for SOME path, e_v → path_lits → conflict.
            # Simplest: emit e_v → path_lits for at least one path.
            # Actually for DAG merging, different paths work differently.
            # Try: emit for each path, per-lit clauses.
            for path in paths:
                for plit in path:
                    emit([-ev, plit])
        else:
            # Transition clauses.
            children = node.get('children', {})
            branch_lits = [k for k in children.keys() if isinstance(k, int)]
            if branch_lits:
                for lit in branch_lits:
                    child = children[lit]
                    # e_v AND (branch var matches lit) → e_child
                    # Clause: ¬e_v ∨ ¬lit ∨ e_child
                    emit([-ev, -lit, e_var[child]])
            elif ('merge',) in children:
                child = children[('merge',)]
                emit([-ev, e_var[child]])

    # Step 3: Derive ¬e_v for each leaf (RUP: state + path → conflict).
    for nid in order:
        node = nodes[nid]
        if not node.get('leaf'):
            continue
        emit([-e_var[nid]])

    # Step 4: Derive ¬e_v for each internal node (RUP: via resolution).
    for nid in order:
        node = nodes[nid]
        if node.get('leaf'):
            continue
        emit([-e_var[nid]])

    # Step 5: Empty clause.
    emit([])

    return count[0]


def emit_drat_rat_sym(n, k, cnf_path, drat_path):
    phase3_bp_paper_sym.MERGE_NODES = True
    cnf, strip_clauses, bp, _, _, _ = build_bp_paper_sym(n, k)

    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, 'w') as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(' '.join(str(l) for l in cl) + ' 0\n')

    with open(drat_path, 'w') as f:
        count = emit_rat_dag_sym(bp, f, max_var)

    return len(bp['nodes']), count


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_paper_rat_sym.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf_path = f"/tmp/strip_sym_rat_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_sym_rat_n{n}_k{k}.drat"

    bp_size, drat_count = emit_drat_rat_sym(n, k, cnf_path, drat_path)

    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    print(
        f"n={n} k={k}: BP DAG {bp_size} nodes, "
        f"CNF {cnf_bytes}B, DRAT {drat_bytes}B ({drat_count} lemmas)"
    )

    result = subprocess.run(
        ['/tmp/drat-trim', cnf_path, drat_path],
        capture_output=True, text=True, timeout=300,
    )
    for line in result.stdout.split('\n'):
        if line.startswith('s '):
            print(f"  {line}")


if __name__ == "__main__":
    main()
