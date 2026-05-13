#!/usr/bin/env python3
"""Paper-ordered UP: propagate in the specific sequence paper describes.

Paper says: at cut j->j+1 transition:
  1. c^{xy}_{i,j}, d^{xy}_{i+1,j} for i+j+1 ∈ [k−log k, k]
  2. If j ∈ [k−Δ, k]: also propagate to o^{xy}_{j−1}
  3. c^{yx}_{j,i}, d^{yx}_{j+1,i} for i+j+1 ∈ [k−log k, k]

In my var encoding:
  paper c^{xy}_{i,j} = cry_c[j, i+j]
  paper d^{xy}_{i,j} = acc_c[j, i+j] for j>=1; pp_c[i,0] for j=0
  paper o^{xy}_i = c_bits[i]
  paper c^{yx}_{i,j} = cry_d[i, i+j]  (d circuit carries)
  paper d^{yx}_{i,j} = acc_d[i, i+j]

We give each variable a priority based on paper's ordering. Canonical UP
picks candidates with smallest priority.
"""


def build_paper_priority(cnf, role2var):
    """Build priority map: var -> priority integer.
    Lower priority = processed first in UP."""
    priorities = {}

    # Priority 0: carries/accumulators in c-circuit (c^{xy}, d^{xy}).
    # Priority 1: outputs in c-circuit (o^{xy}).
    # Priority 2: carries/accumulators in d-circuit.
    # Priority 3: outputs in d-circuit.
    # Priority 4: everything else.

    for v, role in cnf.meta.items():
        if not role:
            continue
        tag = role[0]
        if tag in ('cry_c', 'acc_c'):
            # Sort by column (i+j), then row (j).
            row, col = role[1], role[2]
            pri = (0, col, row, v)
        elif tag == 'c_bit':
            col = role[1]
            pri = (1, col, v)
        elif tag in ('cry_d', 'acc_d'):
            row, col = role[1], role[2]
            pri = (2, col, row, v)
        elif tag == 'd_bit':
            col = role[1]
            pri = (3, col, v)
        else:
            pri = (4, v)
        priorities[v] = pri

    return priorities


def propagate_paper_order(clauses, assign, priorities):
    """Saturate UP with paper-ordered priority.

    Returns (final_assign, conflict_clause, trace).
    """
    assign = dict(assign)
    trace = []

    # Process unit clauses first (sorted by unit-var priority).
    unit_clauses = [cl for cl in clauses if len(cl) == 1]
    unit_clauses.sort(key=lambda cl: priorities.get(abs(cl[0]), (10, abs(cl[0]))))
    for cl in unit_clauses:
        lit = cl[0]
        v = abs(lit)
        val = lit > 0
        if v in assign:
            if assign[v] != val:
                return assign, cl, trace
        else:
            assign[v] = val
            trace.append((v, val, tuple(cl)))

    while True:
        candidates = []
        conflict = None

        for clause in clauses:
            unassigned = []
            satisfied = False
            for lit in clause:
                v = abs(lit)
                if v in assign:
                    val_in = assign[v]
                    lit_val = val_in if lit > 0 else not val_in
                    if lit_val:
                        satisfied = True
                        break
                else:
                    unassigned.append(lit)
            if satisfied:
                continue
            if not unassigned:
                conflict = clause
                break
            if len(unassigned) == 1:
                lit = unassigned[0]
                v = abs(lit)
                val = lit > 0
                candidates.append((v, val, tuple(clause)))

        if conflict is not None:
            return assign, conflict, trace
        if not candidates:
            return assign, None, trace

        # Sort by paper priority, then val, then clause.
        candidates.sort(
            key=lambda c: (priorities.get(c[0], (10, c[0])), c[1], len(c[2]), c[2])
        )
        best = candidates[0]
        v, val, cl = best
        assign[v] = val
        trace.append((v, val, cl))
