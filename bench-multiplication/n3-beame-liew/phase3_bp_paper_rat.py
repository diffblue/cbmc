#!/usr/bin/env python3
"""
RAT extension-variable DAG DRAT emission for paper BP.

For each DAG node v, introduce a fresh extension variable e_v meaning
"the branching program reaches node v".  The BP structure is encoded
via RAT-introduced auxiliary clauses:

  state-to-e:  ¬e_v ∨ ℓ_i          for each state literal ℓ_i of v
  transition:  ¬e_v ∨ ¬V_lit ∨ e_{child}    for branching v with V=value
  merge:       ¬e_v ∨ e_{child}    for non-branching forward merge

We also emit {e_root} as a unit (RAT-introduced while e_root is fresh).
Then we derive ¬e_v for each leaf (RUP via state → CNF conflict), and
bubble ¬e_v up the DAG via resolution on branching variables.  Finally
¬e_root resolves with {e_root} to yield the empty clause.

Proof size: O(|DAG nodes| × |Cut(j)|) for state-to-e clauses, plus
O(|DAG nodes|) for transitions and ¬e_v derivations. This matches
the paper's polynomial claim.
"""

import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import phase3_bp_paper
from phase3_bp_paper import build_bp_paper


def topo_postorder(nodes, root_id=0):
    """Return a list of node ids in post-order (children before parents)."""
    order = []
    visited = set()

    def visit(nid):
        if nid in visited:
            return
        visited.add(nid)
        node = nodes[nid]
        if not node.get('leaf'):
            children = node.get('children', {})
            for k, child_id in children.items():
                visit(child_id)
        order.append(nid)

    visit(root_id)
    return order


def emit_rat_dag(bp, out, max_cnf_var):
    """Emit DAG DRAT via RAT extension variables.

    Returns the number of lemma lines emitted.
    """
    nodes = bp['nodes']
    order = topo_postorder(nodes, 0)

    # Assign fresh extension var for each node.
    e_var = {}
    next_var = max_cnf_var + 1
    for nid in order:
        e_var[nid] = next_var
        next_var += 1

    count = 0

    def emit(lits):
        nonlocal count
        lits = sorted(set(lits), key=lambda x: (abs(x), x))
        if lits:
            out.write(' '.join(str(l) for l in lits) + ' 0\n')
        else:
            out.write('0\n')
        count += 1

    # Step 1: Introduce {e_root} unit (RAT, pivot e_root fresh).
    emit([e_var[0]])

    # Step 2: For each node in post-order, introduce extension var
    # and its defining clauses.
    for nid in order:
        node = nodes[nid]
        ev = e_var[nid]

        # 2a. State-to-e clauses: ¬e_v ∨ ℓ_i for each cut-state literal.
        state = node.get('state') or ()
        for (sv, sval) in state:
            state_lit = sv if sval else -sv
            emit([-ev, state_lit])

        # 2b. Transition clauses to children.
        if node.get('leaf'):
            # No children.
            pass
        else:
            children = node.get('children', {})
            branch_lits = [
                k for k in children.keys() if isinstance(k, int)
            ]
            if branch_lits:
                # Branching node. children[V_lit] = child reached when
                # branching var V has value corresponding to V_lit.
                for lit in branch_lits:
                    child = children[lit]
                    # Clause: ¬e_v ∨ ¬lit ∨ e_{child}
                    # Meaning: if BP at v and the branching literal matches
                    # (i.e. V takes value corresponding to lit), then BP
                    # reaches child.
                    emit([-ev, -lit, e_var[child]])
            elif ('merge',) in children:
                child = children[('merge',)]
                emit([-ev, e_var[child]])

    # Step 3: For each leaf, emit ¬e_v as RUP.
    # Rationale: assume e_v; state-to-e clauses force cut state(v); strip
    # CNF plus state(v) → conflict by UP.
    for nid in order:
        node = nodes[nid]
        if not node.get('leaf'):
            continue
        ev = e_var[nid]
        emit([-ev])

    # Step 4: Bubble ¬e_v up through internal nodes and merges.
    # For a branching v with children c_0, c_1 on variable V (branch_lits
    # ±V), transitions give:
    #   ¬e_v ∨ ¬(+V) ∨ e_{c_pos}   i.e. ¬e_v ∨ -V ∨ e_{c_pos}
    #   ¬e_v ∨ ¬(-V) ∨ e_{c_neg}   i.e. ¬e_v ∨ +V ∨ e_{c_neg}
    # With ¬e_{c_pos} and ¬e_{c_neg} already derived, resolve to get
    #   ¬e_v ∨ -V  and  ¬e_v ∨ +V
    # then resolve to get ¬e_v.
    # For a merge v → child: transition ¬e_v ∨ e_{child} + ¬e_{child} → ¬e_v.
    for nid in order:
        node = nodes[nid]
        if node.get('leaf'):
            continue
        ev = e_var[nid]
        emit([-ev])

    # Step 5: Resolve {e_root} with ¬e_root (both in F now) → ⊥.
    emit([])  # empty clause

    return count


def emit_drat_rat(n, k, cnf_path, drat_path):
    phase3_bp_paper.MERGE_NODES = True  # DAG
    phase3_bp_paper.USE_AUGMENTED_CUT = False  # Paper cut (not augmented)
    cnf, strip_clauses, bp, _, _, _ = build_bp_paper(n, k)

    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, 'w') as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(' '.join(str(l) for l in cl) + ' 0\n')

    with open(drat_path, 'w') as f:
        count = emit_rat_dag(bp, f, max_var)

    return len(bp['nodes']), count


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_paper_rat.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf_path = f"/tmp/strip_paper_rat_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_paper_rat_n{n}_k{k}.drat"

    bp_size, drat_count = emit_drat_rat(n, k, cnf_path, drat_path)

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
