#!/usr/bin/env python3
"""Canonical UP propagation: always derive vars in a fixed order
(smallest var ID first). This makes UP deterministic for a given
saturated sigma, maximizing hash-cons hits in BP construction.

Different paths reaching the same state will produce identical UP
traces when UP is canonical.
"""


def propagate_canonical(clauses, assign, var_index=None):
    """Saturate UP, recording trace in canonical order (smallest var
    derived first at each step).

    Returns (final_assign, conflict_clause, trace).
    trace = list of (var, value, unit_clause_tuple).
    """
    assign = dict(assign)
    trace = []

    # Process unit clauses first.
    unit_clauses = [cl for cl in clauses if len(cl) == 1]
    # Sort unit clauses by var ID for determinism.
    unit_clauses.sort(key=lambda cl: abs(cl[0]))
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
        # Find all candidate UP derivations.
        # For each clause, check if it has exactly one unassigned lit
        # and all others are falsified.
        candidates = []  # (var, val, clause_tuple)
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

        # Canonical choice: smallest var, then preferred value,
        # then smallest-length clause, then smallest lex-order clause.
        candidates.sort(key=lambda c: (c[0], c[1], len(c[2]), c[2]))
        # If multiple candidates derive the same var, check consistency.
        # Pick first in sorted order.
        best = candidates[0]
        v, val, cl = best

        # Check if other candidates derive the opposite value for v.
        for (v2, val2, cl2) in candidates[1:]:
            if v2 == v and val2 != val:
                # Two different clauses force opposite values — conflict.
                # This shouldn't happen in consistent CNF but safety.
                return assign, cl2, trace
            if v2 != v:
                break  # sorted, so no more v

        assign[v] = val
        trace.append((v, val, cl))


def canonicalize_trace(saturated, trace, clauses):
    """Given a saturated assign and any trace, rebuild the trace in
    canonical order (smallest var first). Returns new trace.

    This lets us start with propagate_fast's output (which is fast)
    and canonicalize afterward."""
    # Re-derive from scratch using canonical order.
    _, _, canon_trace = propagate_canonical(clauses, {})
    # Wait, we need to start from the initial (non-propagated) state.
    # But 'saturated' is the final state. Start from initial sigma
    # (= saturated minus trace-derived vars).
    initial = dict(saturated)
    for (v, _, _) in trace:
        if v in initial:
            del initial[v]
    _, _, canon_trace = propagate_canonical(clauses, initial)
    return canon_trace
