#!/usr/bin/env python3
"""
phase3_bp_paper.py — Beame-Liew Lemma 3.2's branching program,
implemented with the paper's exact Cut(j) definition.

Paper reference: arXiv:1705.04302, §3.3, Lemma 3.2 and Corollary 3.3.

Variable mapping (paper ↔ my encoding in generate_array_mul_comm_meta.py):
  paper t^{xy}_{i,j} = my pp_c[i, j]  (a[i] AND b[j])
  paper t^{yx}_{i,j} = my pp_d[i, j]  (b[i] AND a[j])

  paper d^{xy}_{i, j} = sum out of A^{xy}_{i,j} at row j, col (i+j)
                      = my acc_c[j, i+j]    (for j ≥ 1)
                      = my pp_c[i, 0]       (for j = 0; degenerate row-0 wire)
  paper c^{xy}_{i, j} = carry out of A^{xy}_{i,j} at row j, col (i+j)
                      = my cry_c[j, i+j]    (for j ≥ 1)

  Analogous for yx side with acc_d, cry_d, pp_d.

  Output bits:
    paper o^{xy}_i = my c[i]  (returned by array_multiplier)

BP structure (paper's Cut(j)):

Level 0: branch on o^{yx}_i for i in [k-Δ, k], then propagate to d^{yx}_{0, i}.
Level j ≥ 1: branch on t^{xy}_{i, j} for i+j in strip, plus incoming carries
  cL, cR at column k-Δ-1 if they exist. Propagate via UP. Merge on Cut(j+1).
Final level: k+1, all output bits determined; some assignment of Cut(k+1)
  conflicts with an ek inequality clause.

Per-strip BP size: O(k^7 log k) without symmetry preprocessing,
                   O(k^5 log k) with symmetry (Corollary 3.3).

This module implements the Lemma 3.2 version (no symmetry).
"""

import math
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from generate_array_mul_comm_meta import build_commutativity_cnf_meta
from phase3_strip_extract import extract_strip, forced_e_assignment
from fast_propagate import propagate_fast, build_clause_index


# Set to False to disable cut-state merging (builds a tree BP).
# Tree BP is larger but avoids DAG consistency issues in DRAT emission.
MERGE_NODES = False


# -----------------------------------------------------------------------
# Variable lookup by role
# -----------------------------------------------------------------------

def build_role_to_var(cnf):
    """Return dict role -> var."""
    out = {}
    for v, role in cnf.meta.items():
        out[role] = v
    return out


# -----------------------------------------------------------------------
# Paper's Cut(j) definition
# -----------------------------------------------------------------------

def paper_cut(j, k, delta, n, role2var, out_c, out_d):
    """Return the set of CNF variables in paper's Cut(j).

    Paper definitions (§3.3 Lemma 3.2):

    Cut(0) = { d^{yx}_{0, i}, o^{yx}_{i-1} : i-1 in [k-Δ, k] }

    Cut(j) for j in [1, k - log k]:
      { d^{xy}_{i, j-1}, d^{yx}_{j, i-1}  : i+j-1 in [k-Δ, k] }
      { c^{yx}_{j-1, i}                   : i+j-1 in [k-Δ, k-1] }
      { o^{yx}_i                          : i in [k-Δ, k] }

    Cut(j) for j in [k - log k, k]:
      Above, plus { o^{xy}_i : i in [k-Δ, j-1] }
      plus { d^{xy}_{i+1, j-1}, d^{yx}_{j, i}, c^{yx}_{j-1, i}
             : i+j in [k-Δ, k] }
      plus ... (paper's definition)

    For implementation: we iterate the paper's conditions and add the
    corresponding variables (if they exist in the CNF) to the cut.

    The cut is returned as a set of CNF variable IDs.
    """
    cut = set()
    strip_lo = max(0, k - delta)
    strip_hi = k
    log_k = max(1, int(math.log2(max(k, 2))))

    def try_add_role(role):
        v = role2var.get(role)
        if v is not None:
            cut.add(v)

    # Helper: d^{xy}_{i, j} in my naming
    def d_xy(i, jj):
        # Adder A^{xy}_{i, jj} at row jj, column i+jj. Sum = acc_c[jj, i+jj].
        col = i + jj
        if jj == 0:
            # Row-0 wire: d_{i, 0} = t_{i, 0} = pp_c[i, 0]
            if 0 <= i < n:
                return ('pp_c', i, 0)
            return None
        if jj >= 1 and 0 <= col < 2 * n:
            return ('acc_c', jj, col)
        return None

    def d_yx(i, jj):
        col = i + jj
        if jj == 0:
            if 0 <= i < n:
                return ('pp_d', i, 0)
            return None
        if jj >= 1 and 0 <= col < 2 * n:
            return ('acc_d', jj, col)
        return None

    def c_yx(i, jj):
        col = i + jj
        if jj >= 1 and 0 <= col < 2 * n:
            return ('cry_d', jj, col)
        return None

    if j == 0:
        # Cut(0) = {d^{yx}_{0, i}, o^{yx}_{i-1} : i-1 in [k-Δ, k]}
        # i-1 in [k-Δ, k], so i in [k-Δ+1, k+1].
        for i in range(strip_lo + 1, strip_hi + 2):
            role = d_yx(0, i)
            if role:
                try_add_role(role)
            # o^{yx}_{i-1} = out_d[i-1]
            idx = i - 1
            if 0 <= idx < len(out_d):
                cut.add(out_d[idx])
        return cut

    # Base cut (for j in [1, k])
    # d^{xy}_{i, j-1}, d^{yx}_{j, i-1} : i+j-1 in [k-Δ, k]
    # => i in [k-Δ-j+1, k-j+1]
    for i in range(strip_lo - j + 1, strip_hi - j + 2):
        role = d_xy(i, j - 1)
        if role:
            try_add_role(role)
        role = d_yx(j, i - 1)
        if role:
            try_add_role(role)

    # c^{yx}_{j-1, i} : i+j-1 in [k-Δ, k-1]
    # => i in [k-Δ-j+1, k-j]
    for i in range(strip_lo - j + 1, strip_hi - j + 1):
        role = c_yx(j - 1, i)
        if role:
            try_add_role(role)

    # o^{yx}_i : i in [k-Δ, k]
    for i in range(strip_lo, strip_hi + 1):
        if 0 <= i < len(out_d):
            cut.add(out_d[i])

    # Extensions for j in [k - log k, k]
    if j >= k - log_k:
        # o^{xy}_i : i in [k-Δ, j-1]
        for i in range(strip_lo, j):
            if 0 <= i < len(out_c):
                cut.add(out_c[i])
        # d^{xy}_{i+1, j-1}, d^{yx}_{j, i}, c^{yx}_{j-1, i} : i+j in [k-Δ, k]
        # => i in [k-Δ-j, k-j]
        for i in range(strip_lo - j, strip_hi - j + 1):
            role = d_xy(i + 1, j - 1)
            if role:
                try_add_role(role)
            role = d_yx(j, i)
            if role:
                try_add_role(role)
            role = c_yx(j - 1, i)
            if role:
                try_add_role(role)

    return cut


# -----------------------------------------------------------------------
# Branching order per paper
# -----------------------------------------------------------------------

def paper_branch_vars(j, k, delta, n, role2var):
    """Variables to branch on at BP level j (processing row j).

    Per paper §3.3 Inductive Step:
      - t^{xy}_{i, j} for i+j in [k-Δ, k]   (row-j tableau vars of xy)
      - incoming carries cL_{i,j}, cR_{j-1,i} from column k-log k-1
        (only if they exist; the paper's "incoming carry" is the carry
         crossing into the strip from column k-Δ-1)
    """
    out = []
    strip_lo = max(0, k - delta)
    strip_hi = k

    # t^{xy}_{i, j}: my pp_c[i, j] for i+j in strip
    for i in range(max(0, strip_lo - j), min(n, strip_hi - j + 1)):
        role = ('pp_c', i, j)
        v = role2var.get(role)
        if v is not None:
            out.append(v)

    # t^{yx}_{i, j} for j-th row of yx tableau? Actually paper's Lemma 3.2
    # says "tableau variables of circuit R^{yx} simultaneously are revealed"
    # via the symmetry. Without symmetry, we need to branch on them too.
    # Include pp_d at the corresponding positions.
    for i in range(max(0, strip_lo - j), min(n, strip_hi - j + 1)):
        role = ('pp_d', i, j)
        v = role2var.get(role)
        if v is not None:
            out.append(v)

    # Incoming carries at column k-Δ-1, row j (if j ≥ 1)
    if j >= 1:
        col_in = strip_lo - 1
        if col_in >= 1:
            for tag in ('cry_c', 'cry_d'):
                role = (tag, j, col_in)
                v = role2var.get(role)
                if v is not None:
                    out.append(v)

    return out


# -----------------------------------------------------------------------
# Build BP following paper's structure
# -----------------------------------------------------------------------

def build_bp_paper(n, k):
    """Construct BP per paper's Cut(j) definition.

    Returns (cnf, strip_clauses, bp, role2var, out_c, out_d).

    bp is a list of nodes: each node is
      { 'level': j, 'state': frozen_state, 'children': dict,
        'parent': parent_node, 'parent_branch': list of lits,
        'violated_clause': optional leaf indicator }

    We use cumulative propagation but merge only on paper's Cut(j+1).
    """
    cnf, a, b, c_bits, d_bits = build_commutativity_cnf_meta(n)
    role2var = build_role_to_var(cnf)
    delta = max(1, math.ceil(math.log2(max(2 * n, 2))))
    strip_clauses = extract_strip(cnf, k, delta)
    forced_e_units = forced_e_assignment(cnf, k, n)
    strip_clauses = strip_clauses + forced_e_units

    clauses = [list(cl) for cl in strip_clauses]
    var_index = build_clause_index(clauses)

    # Initial assignment: the forced_e unit clauses encode e_i values.
    initial = {}
    for cl in forced_e_units:
        if len(cl) == 1:
            lit = cl[0]
            v = abs(lit)
            initial[v] = 1 if lit > 0 else 0
    initial, _ = propagate_fast(clauses, initial, var_index)

    # BP state: partial assignment dict. We compact states by projecting
    # to Cut(j) at each level.
    levels = []  # list of dicts: state_key -> node_id
    nodes = []   # list of (level, state_key, parent_id, branch_lit, assignment)

    root_state = freeze_cut_state(initial, paper_cut(0, k, delta, n,
                                                     role2var, c_bits, d_bits))
    levels.append({root_state: 0})
    nodes.append({
        'level': 0, 'state': root_state, 'parent': None,
        'branch_lit': None, 'assign': initial, 'children': {},
        'leaf': False, 'violated': None,
    })

    # Process BP level by level.
    frontier = [0]  # list of node ids at current level
    for j in range(0, k + 2):
        cut_j_vars = paper_cut(j + 1, k, delta, n,
                               role2var, c_bits, d_bits) \
                     if j < k + 1 else set()
        branch_vars = paper_branch_vars(j, k, delta, n, role2var) \
                      if j < k + 1 else []
        # Filter branch vars to those not already assigned.
        new_frontier_map = {}  # state_key -> node_id
        for node_id in frontier:
            node = nodes[node_id]
            if node.get('leaf'):
                continue
            # Expand: branch on each unassigned branch_var in sequence.
            expand(node, branch_vars, clauses, var_index,
                   cut_j_vars, new_frontier_map, nodes, node_id,
                   depth=0, max_depth=len(branch_vars))
        levels.append(new_frontier_map)
        frontier = list(new_frontier_map.values())
        if not frontier:
            break

    bp = {
        'nodes': nodes,
        'levels': levels,
        'delta': delta,
        'strip_lo': max(0, k - delta),
        'strip_hi': k,
    }
    return cnf, strip_clauses, bp, role2var, c_bits, d_bits


def expand(node, branch_vars, clauses, var_index, cut_vars,
           level_map, nodes, parent_id, depth, max_depth):
    """Recursively branch on branch_vars[depth:], creating children.
    When all branch_vars are exhausted OR a conflict is found, merge
    into level_map by cut state.
    """
    assign = node['assign']
    # Propagate first.
    new_assign, confl = propagate_fast(clauses, assign, var_index)

    if confl is not None:
        # Leaf (conflict). Mark the node; don't descend further.
        node['leaf'] = True
        node['violated'] = confl
        node['assign'] = new_assign
        return

    node['assign'] = new_assign

    # Find next unassigned branch var.
    next_var = None
    for v in branch_vars[depth:]:
        if v not in new_assign:
            next_var = v
            break

    if next_var is None:
        # No more branching at this level. Merge on Cut.
        state = freeze_cut_state(new_assign, cut_vars)
        if MERGE_NODES and state in level_map:
            child_id = level_map[state]
            node['children'][('merge',)] = child_id
        else:
            child_id = len(nodes)
            if MERGE_NODES:
                level_map[state] = child_id
            else:
                # Tree mode: use unique keys so every child is kept.
                level_map[('tree', child_id)] = child_id
            nodes.append({
                'level': nodes[parent_id]['level'] + 1,
                'state': state, 'parent': parent_id,
                'branch_lit': None, 'assign': dict(new_assign),
                'children': {}, 'leaf': False, 'violated': None,
            })
            node['children'][('merge',)] = child_id
        return

    # Branch on next_var: two children (val=0, val=1).
    for val in (0, 1):
        branch_assign = dict(new_assign)
        branch_assign[next_var] = val
        lit = next_var if val == 1 else -next_var
        child_node = {
            'level': node['level'], 'state': None, 'parent': parent_id,
            'branch_lit': lit, 'assign': branch_assign,
            'children': {}, 'leaf': False, 'violated': None,
        }
        child_id = len(nodes)
        nodes.append(child_node)
        node['children'][lit] = child_id
        expand(child_node, branch_vars, clauses, var_index, cut_vars,
               level_map, nodes, child_id, depth + 1, max_depth)


def freeze_cut_state(assign, cut_vars):
    """Project assignment to cut_vars, return a hashable key."""
    items = []
    for v in sorted(cut_vars):
        if v in assign:
            items.append((v, assign[v]))
    return tuple(items)


# -----------------------------------------------------------------------
# Stats / debugging
# -----------------------------------------------------------------------

def summarize_bp(bp, n, k):
    nodes = bp['nodes']
    by_level = defaultdict(int)
    leaves = 0
    for node in nodes:
        by_level[node['level']] += 1
        if node.get('leaf'):
            leaves += 1
    print(f"BP for n={n}, k={k}: {len(nodes)} total nodes, {leaves} leaves")
    for lv in sorted(by_level):
        print(f"  level {lv}: {by_level[lv]} nodes")


def main():
    if len(sys.argv) < 3:
        print("usage: phase3_bp_paper.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])
    cnf, strip_clauses, bp, role2var, out_c, out_d = build_bp_paper(n, k)
    summarize_bp(bp, n, k)


if __name__ == "__main__":
    main()
