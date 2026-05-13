#!/usr/bin/env python3
"""
Paper BP on the symmetry-substituted CNF (Corollary 3.3).

After pp_d → pp_c substitution, BP branches only on one side (pp_c),
and paper's Cut(j) as defined in Lemma 3.2 applies directly
without dual-side augmentation.

Expected per-strip size: O(k^5 log k) per Corollary 3.3.
"""

import math
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from generate_sym_mul_comm_meta import symmetry_substituted_cnf
from phase3_strip_extract import extract_strip, forced_e_assignment, strip_delta
from fast_propagate import propagate_fast, build_clause_index


MERGE_NODES = True   # Enable DAG merging (safe now with one-sided cut)


def build_role_to_var(cnf):
    out = {}
    for v, role in cnf.meta.items():
        out[role] = v
    return out


def paper_cut_onesided(j, k, delta, n, role2var, out_c, out_d):
    """Paper's Cut(j) for the SYMMETRY-SUBSTITUTED CNF.

    With pp_d substituted away, the "yx" tableau is the same as "xy"
    with transposed indices. Paper's Cut(j) then applies naturally.

    For j in [1, k - log k]:
      - d^{xy}_{i, j-1}  for i+j-1 in [k-Δ, k]          (row j-1 sums)
      - d^{yx}_{j, i-1}  for i+j-1 in [k-Δ, k]          (row j sums of yx)
      - c^{yx}_{j-1, i}  for i+j-1 in [k-Δ, k-1]        (row j-1 carries of yx)
      - o^{yx}_i         for i in [k-Δ, k]              (output bits of yx)

    d^{xy}_{i, j-1} maps to acc_c[j-1, i+j-1] in my encoding.
    d^{yx}_{j, i-1} maps to acc_d[j, i+j-1] in my encoding.
    """
    cut = set()
    strip_lo = max(0, k - delta)
    strip_hi = k
    log_k = max(1, int(math.log2(max(k, 2))))

    def try_add_role(role):
        v = role2var.get(role)
        if v is not None:
            cut.add(v)

    def d_xy(i, jj):
        col = i + jj
        if jj == 0:
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
                # After sym sub, pp_d[0, i] = pp_c[i, 0]
                return ('pp_c', i, 0)
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
        for i in range(strip_lo + 1, strip_hi + 2):
            role = d_yx(0, i)
            if role:
                try_add_role(role)
            idx = i - 1
            if 0 <= idx < len(out_d):
                cut.add(out_d[idx])
        return cut

    # Base cut (for j in [1, k])
    for i in range(strip_lo - j + 1, strip_hi - j + 2):
        role = d_xy(i, j - 1)
        if role:
            try_add_role(role)
        role = d_yx(j, i - 1)
        if role:
            try_add_role(role)

    for i in range(strip_lo - j + 1, strip_hi - j + 1):
        role = c_yx(j - 1, i)
        if role:
            try_add_role(role)

    for i in range(strip_lo, strip_hi + 1):
        if 0 <= i < len(out_d):
            cut.add(out_d[i])

    if j >= k - log_k:
        for i in range(strip_lo, j):
            if 0 <= i < len(out_c):
                cut.add(out_c[i])
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


def paper_branch_vars_onesided(j, k, delta, n, role2var):
    """Branching order: pp_c row-j vars (no pp_d since substituted)."""
    out = []
    strip_lo = max(0, k - delta)
    strip_hi = k

    for i in range(max(0, strip_lo - j), min(n, strip_hi - j + 1)):
        role = ('pp_c', i, j)
        v = role2var.get(role)
        if v is not None:
            out.append(v)

    # Incoming carries at col k-Δ-1 (for row j)
    if j >= 1:
        col_in = strip_lo - 1
        if col_in >= 1:
            for tag in ('cry_c', 'cry_d'):
                role = (tag, j, col_in)
                v = role2var.get(role)
                if v is not None:
                    out.append(v)
    return out


def freeze_cut_state(assign, cut_vars):
    items = []
    for v in sorted(cut_vars):
        if v in assign:
            items.append((v, assign[v]))
    return tuple(items)


# Adapted strip extraction for sym CNF (reuse core logic, CNF has same roles)
def extract_strip_sym(cnf, k, delta):
    """Same as extract_strip but handles post-sym CNF (may need cnf-shim)."""
    return extract_strip(cnf, k, delta)


def forced_e_assignment_sym(cnf, k, n):
    return forced_e_assignment(cnf, k, n)


def build_bp_paper_sym(n, k):
    """Paper BP on symmetry-substituted CNF."""
    cnf, a, b, c_bits, d_bits = symmetry_substituted_cnf(n)
    role2var = build_role_to_var(cnf)
    delta = max(1, math.ceil(math.log2(max(2 * n, 2))))

    strip_clauses = extract_strip_sym(cnf, k, delta)
    forced_e_units = forced_e_assignment_sym(cnf, k, n)
    strip_clauses = strip_clauses + forced_e_units

    clauses = [list(cl) for cl in strip_clauses]
    var_index = build_clause_index(clauses)

    initial = {}
    for cl in forced_e_units:
        if len(cl) == 1:
            lit = cl[0]
            v = abs(lit)
            initial[v] = 1 if lit > 0 else 0
    initial, _ = propagate_fast(clauses, initial, var_index)

    root_state = freeze_cut_state(
        initial,
        paper_cut_onesided(0, k, delta, n, role2var, c_bits, d_bits),
    )
    levels = [{root_state: 0}]
    nodes = [{
        'level': 0, 'state': root_state, 'parent': None,
        'branch_lit': None, 'assign': dict(initial),
        'children': {}, 'leaf': False, 'violated': None,
    }]

    def expand(node, branch_vars, cut_vars, level_map, parent_id,
               depth):
        assign = node['assign']
        new_assign, confl = propagate_fast(clauses, assign, var_index)

        if confl is not None:
            node['leaf'] = True
            node['violated'] = confl
            node['assign'] = new_assign
            node['state'] = freeze_cut_state(new_assign, cut_vars)
            return

        node['assign'] = new_assign

        next_var = None
        for v in branch_vars[depth:]:
            if v not in new_assign:
                next_var = v
                break

        if next_var is None:
            state = freeze_cut_state(new_assign, cut_vars)
            if MERGE_NODES and state in level_map:
                child_id = level_map[state]
                node['children'][('merge',)] = child_id
            else:
                child_id = len(nodes)
                key = state if MERGE_NODES else ('tree', child_id)
                level_map[key] = child_id
                nodes.append({
                    'level': nodes[parent_id]['level'] + 1,
                    'state': state, 'parent': parent_id,
                    'branch_lit': None, 'assign': dict(new_assign),
                    'children': {}, 'leaf': False, 'violated': None,
                })
                node['children'][('merge',)] = child_id
            return

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
            expand(child_node, branch_vars, cut_vars,
                   level_map, child_id, depth + 1)

    frontier = [0]
    for j in range(0, k + 2):
        cut_j_vars = paper_cut_onesided(
            j + 1, k, delta, n, role2var, c_bits, d_bits
        ) if j < k + 1 else set()
        branch_vars = paper_branch_vars_onesided(
            j, k, delta, n, role2var
        ) if j < k + 1 else []
        new_frontier_map = {}
        for node_id in frontier:
            node = nodes[node_id]
            if node.get('leaf'):
                continue
            expand(node, branch_vars, cut_j_vars, new_frontier_map,
                   node_id, depth=0)
        frontier = list(new_frontier_map.values())
        if not frontier:
            break

    bp = {
        'nodes': nodes, 'delta': delta,
        'strip_lo': max(0, k - delta), 'strip_hi': k,
    }
    return cnf, strip_clauses, bp, role2var, c_bits, d_bits


def main():
    if len(sys.argv) < 3:
        print("usage: phase3_bp_paper_sym.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])
    cnf, strip_clauses, bp, _, _, _ = build_bp_paper_sym(n, k)
    total = len(bp['nodes'])
    leaves = sum(1 for n_ in bp['nodes'] if n_.get('leaf'))
    print(f"n={n} k={k}: sym BP {total} nodes ({leaves} leaves)")


if __name__ == "__main__":
    main()
