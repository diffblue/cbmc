"""
Fast unit propagation with clause-variable index.

Drop-in replacement for phase3_bp_paper_order.propagate().
"""

from collections import defaultdict


def build_clause_index(clauses):
    """Return dict: var -> list of (clause_id, clause_list)."""
    idx = defaultdict(list)
    for i, cl in enumerate(clauses):
        for lit in cl:
            idx[abs(lit)].append((i, cl))
    return idx


def propagate_fast(clauses, assign, var_index=None):
    """Watched-literal-style UP: for each newly-assigned var, only
    re-check clauses containing that var. Return (final, conflict).
    """
    assign = dict(assign)
    if var_index is None:
        var_index = build_clause_index(clauses)

    pending = list(assign.keys())

    # Process unit clauses first: they must be assigned.
    for cl in clauses:
        if len(cl) == 1:
            lit = cl[0]
            vv = abs(lit)
            new_val = lit > 0
            if vv in assign:
                if assign[vv] != new_val:
                    return assign, cl
            else:
                assign[vv] = new_val
                pending.append(vv)

    while pending:
        v = pending.pop()
        for cid, cl in var_index.get(v, ()):
            unassigned = []
            satisfied = False
            for lit in cl:
                vv = abs(lit)
                if vv in assign:
                    val = assign[vv] if lit > 0 else not assign[vv]
                    if val:
                        satisfied = True
                        break
                else:
                    unassigned.append(lit)
            if satisfied:
                continue
            if not unassigned:
                return assign, cl
            if len(unassigned) == 1:
                lit = unassigned[0]
                vv = abs(lit)
                new_val = lit > 0
                if vv in assign:
                    if assign[vv] != new_val:
                        return assign, cl
                    continue
                assign[vv] = new_val
                pending.append(vv)
    return assign, None
