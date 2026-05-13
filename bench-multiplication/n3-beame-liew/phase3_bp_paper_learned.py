#!/usr/bin/env python3
"""
DAG DRAT emission where each leaf's "state" is computed via conflict
clause learning from the UP trace. The minimal essential assignment
that guarantees UP-refutation is used as the leaf's clause.

Then DAG merging on these minimal states gives consistent clauses.
RUP validation: each leaf's minimal-state-negation clause is RUP
(CNF + minimal state UP-refutes because trace produces conflict).

For internal nodes: resolve children's minimal-state clauses.

This is the core Prop 2.1 construction but using derived "1UIP-like"
conflict clauses at leaves.
"""

import math
import os
import subprocess
import sys
from collections import defaultdict

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


def learn_conflict_clause(violated_clause, trace, assign):
    """Given a violated CNF clause and a UP trace, walk backward
    through the trace resolving on each UP-derived variable.
    Returns the learned clause (= negation of minimal assignment).

    The learned clause contains only literals NOT derived by UP — so
    it's based on the "root cause" branching/forced assignment.
    """
    # trace is a list of (var, val, unit_clause) in order of derivation.
    # Build a lookup: var -> (val, unit_clause)
    reason = {}
    for (var, val, unit_cl) in trace:
        reason[var] = (val, unit_cl)

    # Current clause starts as violated clause.
    current = set(violated_clause)

    # Process UP-derived literals in REVERSE order (most recent first).
    for (var, val, unit_cl) in reversed(trace):
        # If current clause contains literal of var (with opposite polarity
        # to derived value), resolve on var.
        # Derived val → literal is (+var if val else -var) in unit_cl.
        lit_in_reason = var if val else -var
        # Opposite of derived lit in current clause means the UP-derived
        # value makes that literal false — resolve to eliminate.
        opposite = -lit_in_reason
        if opposite in current:
            # Resolve: current - {opposite} ∪ (unit_cl - {lit_in_reason})
            new_current = (current - {opposite}) | (
                set(unit_cl) - {lit_in_reason}
            )
            current = new_current

    return frozenset(current)


def build_bp_and_learn(n, k):
    """Build sym DAG BP with minimal leaf clauses via conflict analysis."""
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

    # Initial trace from forced_e.
    initial = {}
    for cl in forced_e_units:
        if len(cl) == 1:
            lit = cl[0]
            initial[abs(lit)] = lit > 0
    initial_trace = []
    initial, _ = propagate_fast(
        clauses, initial, var_index, trace=initial_trace
    )

    nodes = []
    root_cut = paper_cut_onesided(0, k, delta, n, role2var, c_bits, d_bits)
    root_state = freeze_cut_state(initial, root_cut)

    # A node has:
    # For internal: 'kind'='branch', 'var', 'children': {lit: child_id}
    # For merge: 'kind'='merge', 'target': child_id
    # For leaf: 'kind'='leaf', 'learned': frozenset(learned clause)
    nodes.append({
        'kind': 'initial', 'state': root_state,
        'assign': dict(initial), 'level': 0,
        'cumulative_trace': list(initial_trace),
        'children': {},
    })

    def expand(nid, branch_vars, cut_vars, depth, new_frontier):
        node = nodes[nid]
        assign = node['assign']
        cumtrace = list(node.get('cumulative_trace', []))

        trace_here = []
        new_assign, confl = propagate_fast(
            clauses, assign, var_index, trace=trace_here
        )
        cumtrace.extend(trace_here)

        if confl is not None:
            learned = learn_conflict_clause(
                confl, cumtrace, new_assign
            )
            node['kind'] = 'leaf'
            node['learned'] = learned
            node['assign'] = new_assign
            return

        # Find next branching var.
        next_var = None
        for v in branch_vars[depth:]:
            if v not in new_assign:
                next_var = v
                break

        if next_var is None:
            # Merge.
            merged_state = freeze_cut_state(new_assign, cut_vars)
            if merged_state in new_frontier:
                target_id = new_frontier[merged_state]
            else:
                target_id = len(nodes)
                nodes.append({
                    'kind': 'initial',
                    'state': merged_state,
                    'assign': dict(new_assign),
                    'level': node['level'] + 1,
                    'cumulative_trace': cumtrace,
                    'children': {},
                })
                new_frontier[merged_state] = target_id
            node['kind'] = 'merge'
            node['target'] = target_id
            return

        # Branching.
        node['kind'] = 'branch'
        node['var'] = next_var
        node['assign'] = new_assign
        node['cumulative_trace'] = cumtrace
        node['children'] = {}

        for val in (0, 1):
            child_assign = dict(new_assign)
            child_assign[next_var] = val
            lit = next_var if val == 1 else -next_var
            child_id = len(nodes)
            nodes.append({
                'kind': 'initial',
                'state': None,
                'assign': child_assign,
                'level': node['level'],
                'cumulative_trace': list(cumtrace),  # inherit
                'children': {},
            })
            node['children'][lit] = child_id
            expand(child_id, branch_vars, cut_vars, depth + 1, new_frontier)

    frontier = {root_state: 0}
    for j in range(0, k + 2):
        if not frontier:
            break
        cut_j_vars = paper_cut_onesided(
            j + 1, k, delta, n, role2var, c_bits, d_bits
        ) if j < k + 1 else set()
        branch_vars = paper_branch_vars_onesided(
            j, k, delta, n, role2var
        ) if j < k + 1 else []

        new_frontier = {}
        for state, nid in frontier.items():
            expand(nid, branch_vars, cut_j_vars, 0, new_frontier)
        frontier = new_frontier

    return cnf, strip_clauses, nodes


def emit_drat_learned(nodes, out):
    """Emit DRAT by resolving up through the BP using learned clauses
    at leaves."""
    clause_of = {}
    emitted = set()
    axioms = set()  # These are CNF clauses, already in F.

    def emit(cl):
        cl = frozenset(cl)
        if cl in emitted or cl in axioms:
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
            learned = node['learned']
            # Emit as RUP.
            emit(learned)
            clause_of[nid] = learned
            return learned

        if kind == 'merge':
            target = node.get('target')
            c = post(target)
            clause_of[nid] = c
            return c

        if kind == 'branch':
            var = node['var']
            children = node.get('children', {})
            c_neg = post(children.get(-var))
            c_pos = post(children.get(var))
            if c_neg is None or c_pos is None:
                clause_of[nid] = None
                return None

            # c_neg is from V=F branch. Its clause should contain +var
            # (because +var is in the forbidden assignment that reaches c_neg).
            # c_pos should contain -var.
            if var in c_neg and -var in c_pos:
                res = frozenset((c_neg - {var}) | (c_pos - {-var}))
                emit(res)
            elif -var in c_neg and var in c_pos:
                res = frozenset((c_neg - {-var}) | (c_pos - {var}))
                emit(res)
            elif var not in c_neg and -var not in c_neg:
                res = c_neg
            elif var not in c_pos and -var not in c_pos:
                res = c_pos
            else:
                res = c_neg & c_pos
                if res != c_neg and res != c_pos:
                    emit(res)
            clause_of[nid] = res
            return res

        clause_of[nid] = None
        return None

    root_cl = post(0)
    if root_cl and root_cl != frozenset():
        # Root clause should have resolved to empty; if not, something's off.
        if frozenset() not in emitted:
            out.write('0\n')


def emit_drat_learn(n, k, cnf_path, drat_path):
    cnf, strip_clauses, nodes = build_bp_and_learn(n, k)
    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, 'w') as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(' '.join(str(l) for l in cl) + ' 0\n')
    with open(drat_path, 'w') as f:
        emit_drat_learned(nodes, f)
    return len(nodes)


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_paper_learned.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf_path = f"/tmp/strip_learn_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_learn_n{n}_k{k}.drat"
    bp_size = emit_drat_learn(n, k, cnf_path, drat_path)

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
