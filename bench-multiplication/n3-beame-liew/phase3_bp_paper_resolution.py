#!/usr/bin/env python3
"""
Resolution-based DRAT emission on sym DAG BP (Prop 2.1 proper).

For each BP node, compute clause(v) via resolution:
- Leaf v: clause(v) = the violated CNF clause (an axiom; no emission).
- UP-propagation step at v (derived x=b via unit clause U):
    clause(v) = resolve(clause(child), U, x)
- Branching at v on variable V (children c0 = V=F, c1 = V=T):
    clause(v) = resolve(clause(c0), clause(c1), V)
- Merge at v (single target): clause(v) = clause(target).

Each clause is emitted once (DAG shares merged subtrees).

For this approach, we need to UNBUNDLE the UP propagation — each UP
step becomes a separate emitted resolvent.

Implementation plan:
1. Build sym DAG BP with UP traces stored at each edge.
2. Walk BP bottom-up, computing and emitting clauses at each step.
3. Merge nodes produce single clause shared by all incoming paths.
"""

import math
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from generate_sym_mul_comm_meta import symmetry_substituted_cnf
from phase3_strip_extract import extract_strip, forced_e_assignment
from phase3_bp_paper_sym import paper_cut_onesided, paper_branch_vars_onesided
from fast_propagate import propagate_fast, build_clause_index


def freeze_cut_state(assign, cut_vars):
    items = []
    for v in sorted(cut_vars):
        if v in assign:
            items.append((v, assign[v]))
    return tuple(items)


def build_bp_with_trace(n, k):
    """Build DAG BP where each edge records the UP-propagation trace."""
    cnf, a, b, c_bits, d_bits = symmetry_substituted_cnf(n)
    delta = max(1, math.ceil(math.log2(max(2 * n, 2))))

    strip_clauses = extract_strip(cnf, k, delta)
    forced_e_units = forced_e_assignment(cnf, k, n)
    strip_clauses = strip_clauses + forced_e_units

    clauses = [list(cl) for cl in strip_clauses]
    var_index = build_clause_index(clauses)

    role2var = {}
    for v, role in cnf.meta.items():
        role2var[role] = v

    # Initial assignment from forced_e.
    initial = {}
    for cl in forced_e_units:
        if len(cl) == 1:
            lit = cl[0]
            initial[abs(lit)] = lit > 0

    # Propagate initial state with trace.
    initial_trace = []
    initial, _ = propagate_fast(clauses, initial, var_index,
                                trace=initial_trace)

    # Root state.
    root_cut = paper_cut_onesided(0, k, delta, n, role2var, c_bits, d_bits)
    root_state = freeze_cut_state(initial, root_cut)

    # Nodes: list of dicts.
    # Each node has:
    #   'kind': 'branch' | 'leaf' | 'merge'
    #   'state': cut-state tuple
    #   'level': int
    #   For 'branch': 'var', 'children': {lit -> (child_id, trace)}
    #   For 'leaf': 'violated' (CNF clause), 'assign'
    #   For 'merge': 'target' (child_id)
    nodes = []

    def new_node(**kwargs):
        nodes.append(kwargs)
        return len(nodes) - 1

    root_id = new_node(
        kind='initial',
        state=root_state,
        assign=dict(initial),
        level=0,
        initial_trace=initial_trace,
        children={},
    )

    # BFS: process level by level.
    frontier = {root_state: root_id}

    for j in range(0, k + 2):
        if not frontier:
            break
        cut_j_vars = paper_cut_onesided(
            j + 1, k, delta, n, role2var, c_bits, d_bits
        ) if j < k + 1 else set()
        branch_vars = paper_branch_vars_onesided(
            j, k, delta, n, role2var
        ) if j < k + 1 else []

        # New frontier for next level: cut-state -> node_id
        new_frontier = {}

        for node_state, node_id in frontier.items():
            parent_node = nodes[node_id]
            parent_assign = parent_node['assign']

            # Expand this node by branching.
            expand_node(
                parent_node, parent_id=node_id,
                branch_vars=branch_vars, cut_vars=cut_j_vars,
                clauses=clauses, var_index=var_index,
                nodes=nodes, new_frontier=new_frontier, depth=0,
            )

        frontier = new_frontier

    return cnf, strip_clauses, nodes, root_id


def expand_node(node, parent_id, branch_vars, cut_vars, clauses,
                var_index, nodes, new_frontier, depth):
    """Recursively branch on branch_vars, creating children with UP traces."""
    assign = node['assign']

    # First: propagate with trace.
    trace = []
    new_assign, confl = propagate_fast(clauses, assign, var_index,
                                        trace=trace)

    if confl is not None:
        # Turn current node into a leaf.
        node['kind'] = 'leaf'
        node['violated'] = tuple(confl)
        node['assign'] = new_assign
        node['trace'] = trace
        return

    # Find next unassigned branch var.
    next_var = None
    for v in branch_vars[depth:]:
        if v not in new_assign:
            next_var = v
            break

    if next_var is None:
        # All branch vars assigned. Merge on cut state.
        merged_state = freeze_cut_state(new_assign, cut_vars)
        if merged_state in new_frontier:
            target_id = new_frontier[merged_state]
        else:
            target_id = len(nodes)
            nodes.append({
                'kind': 'initial',  # placeholder, will be expanded next level
                'state': merged_state,
                'assign': dict(new_assign),
                'level': node['level'] + 1,
                'initial_trace': trace,
                'children': {},
            })
            new_frontier[merged_state] = target_id

        # Mark current node as propagation-to-merge
        node['kind'] = 'merge'
        node['target'] = target_id
        node['trace'] = trace
        return

    # Branching node.
    node['kind'] = 'branch'
    node['var'] = next_var
    node['trace'] = trace  # UP done before branching
    node['assign'] = new_assign
    node['children'] = {}

    for val in (0, 1):
        branch_assign = dict(new_assign)
        branch_assign[next_var] = val
        lit = next_var if val == 1 else -next_var

        child_id = len(nodes)
        nodes.append({
            'kind': 'initial',
            'state': None,
            'assign': branch_assign,
            'level': node['level'],
            'trace': [],
            'children': {},
        })
        node['children'][lit] = child_id
        expand_node(
            nodes[child_id], child_id,
            branch_vars, cut_vars, clauses, var_index,
            nodes, new_frontier, depth + 1,
        )


def emit_drat_resolution(nodes, strip_clauses, out):
    """Emit DRAT by walking BP bottom-up and emitting resolution steps.

    Clause at each node is ¬path-to-node (for non-merged) or more
    complex for merged nodes. We compute clause(v) as:
    - Leaf: violated CNF clause (axiom, no emit)
    - Branch on V with children c0 (V=F), c1 (V=T):
        clause(v) = resolve(clause(c0), clause(c1), V)
    - Merge to target: clause(v) = clause(target)

    UP propagation along edges is ignored at this level — the "clause
    at v" encompasses the cumulative resolution of the subtree.
    """
    clause_of = {}
    emitted = set()

    def emit(cl):
        cl = frozenset(cl)
        if cl in emitted:
            return
        lits = sorted(cl, key=lambda x: (abs(x), x))
        if lits:
            out.write(' '.join(str(l) for l in lits) + ' 0\n')
        else:
            out.write('0\n')
        emitted.add(cl)

    def post(nid):
        if nid in clause_of:
            return clause_of[nid]

        node = nodes[nid]
        kind = node.get('kind')

        if kind == 'leaf':
            cl = frozenset(node['violated'])
            clause_of[nid] = cl
            # Axiom; no emit.
            return cl

        if kind == 'merge':
            target = node.get('target')
            if target is not None:
                c = post(target)
                clause_of[nid] = c
                return c
            clause_of[nid] = None
            return None

        if kind == 'branch':
            var = node['var']
            children = node.get('children', {})
            c_neg = post(children.get(-var))  # V=F
            c_pos = post(children.get(var))   # V=T
            if c_neg is None or c_pos is None:
                clause_of[nid] = None
                return None

            # c_neg came from V=F branch. For this branch to reach conflict,
            # path contains -var (or V-derived implications); its clause
            # contains +var as literal (since falsified by V=F).
            # c_pos from V=T branch contains -var similarly.
            if var in c_neg and -var in c_pos:
                res = frozenset((c_neg - {var}) | (c_pos - {-var}))
            elif -var in c_neg and var in c_pos:
                res = frozenset((c_neg - {-var}) | (c_pos - {var}))
            elif var not in c_neg and -var not in c_neg:
                # c_neg doesn't contain var; use as-is (it's stronger).
                res = c_neg
            elif var not in c_pos and -var not in c_pos:
                res = c_pos
            else:
                # Same polarity; use intersection.
                res = c_neg & c_pos

            clause_of[nid] = res
            emit(res)
            return res

        if kind == 'initial':
            # Shouldn't reach here if BP construction is complete.
            clause_of[nid] = None
            return None

        clause_of[nid] = None
        return None

    root_cl = post(0)
    if root_cl and frozenset() not in emitted:
        out.write('0\n')
        emitted.add(frozenset())


def emit_drat_sym_prop21(n, k, cnf_path, drat_path):
    cnf, strip_clauses, nodes, root_id = build_bp_with_trace(n, k)
    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, 'w') as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(' '.join(str(l) for l in cl) + ' 0\n')
    with open(drat_path, 'w') as f:
        emit_drat_resolution(nodes, strip_clauses, f)
    return len(nodes)


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_paper_resolution.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf_path = f"/tmp/strip_res_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_res_n{n}_k{k}.drat"
    bp_size = emit_drat_sym_prop21(n, k, cnf_path, drat_path)

    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n} k={k}: BP {bp_size} nodes, "
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
