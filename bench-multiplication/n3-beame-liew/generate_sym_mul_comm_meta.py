#!/usr/bin/env python3
"""
Build commutativity CNF with symmetry substitution:
replace each pp_d[j, i] variable with pp_c[i, j] (tableau symmetry).

This is the preprocessing used in Beame-Liew Corollary 3.3 to get
O(k^5 log k) per strip instead of O(k^7 log k) in Lemma 3.2.

After substitution, the BP branches only on one side (pp_c), and
paper's Cut(j) definition (which is one-sided) becomes applicable.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from generate_array_mul_comm_meta import build_commutativity_cnf_meta


def symmetry_substituted_cnf(n):
    """Build the commutativity CNF then substitute pp_d[j, i] with
    pp_c[i, j]. The resulting CNF has the same truth value but fewer
    variables (pp_d vars are eliminated).
    """
    cnf, a, b, c_bits, d_bits = build_commutativity_cnf_meta(n)

    # Build substitution map: pp_d[j, i] → pp_c[i, j]
    pp_c_map = {}
    pp_d_map = {}
    for v, role in cnf.meta.items():
        if role is None:
            continue
        if role[0] == "pp_c":
            pp_c_map[(role[1], role[2])] = v
        elif role[0] == "pp_d":
            pp_d_map[(role[1], role[2])] = v

    # subst[v] = v' means replace v with v' in all clauses
    subst = {}
    for (j, i), pd in pp_d_map.items():
        # pp_d[j, i] = b[j] ∧ a[i] = a[i] ∧ b[j] = pp_c[i, j]
        key = (i, j)
        if key in pp_c_map:
            subst[pd] = pp_c_map[key]

    # Apply substitution to clauses.
    new_clauses = []
    for cl in cnf.clauses:
        new_cl = []
        skip = False
        for lit in cl:
            v = abs(lit)
            sign = 1 if lit > 0 else -1
            if v in subst:
                new_v = subst[v]
                new_cl.append(sign * new_v)
            else:
                new_cl.append(lit)
        # Remove duplicates and detect tautologies
        seen = {}
        is_taut = False
        for lit in new_cl:
            if -lit in seen:
                is_taut = True
                break
            seen[lit] = True
        if is_taut:
            continue
        # Deduplicate
        dedup_cl = list(dict.fromkeys(new_cl))
        new_clauses.append(dedup_cl)

    # Remove pp_d vars from meta.
    new_meta = {}
    for v, role in cnf.meta.items():
        if v in subst:
            continue  # Skip the substituted pp_d var
        new_meta[v] = role

    # Reindex variables (compact the var space).
    old_to_new = {}
    next_var = 1
    for v in sorted(new_meta.keys()):
        old_to_new[v] = next_var
        next_var += 1

    final_clauses = []
    for cl in new_clauses:
        new_cl = []
        for lit in cl:
            v = abs(lit)
            sign = 1 if lit > 0 else -1
            if v in old_to_new:
                new_cl.append(sign * old_to_new[v])
            else:
                # Var not in meta? Keep as-is (shouldn't happen after subst)
                new_cl.append(lit)
        final_clauses.append(new_cl)

    final_meta = {}
    for old_v, role in new_meta.items():
        final_meta[old_to_new[old_v]] = role

    # Remap a, b, c, d variable lists.
    def remap(v):
        """Apply substitution then old_to_new mapping."""
        if v in subst:
            v = subst[v]
        if v in old_to_new:
            return old_to_new[v]
        return v

    new_a = [remap(v) for v in a]
    new_b = [remap(v) for v in b]
    new_c = [remap(v) for v in c_bits]
    new_d = [remap(v) for v in d_bits]

    # Create a new CNF builder holder.
    class CnfShim:
        def __init__(self):
            self.clauses = final_clauses
            self.meta = final_meta
            self.next_var = max(final_meta.keys()) + 1 if final_meta else 1

    shim = CnfShim()
    return shim, new_a, new_b, new_c, new_d


def main():
    if len(sys.argv) != 2:
        print("usage: generate_sym_mul_comm_meta.py N", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])

    cnf_orig, *_ = build_commutativity_cnf_meta(n)
    cnf_sym, a, b, c, d = symmetry_substituted_cnf(n)

    print(f"n={n}:")
    print(f"  Original: {cnf_orig.next_var - 1} vars, "
          f"{len(cnf_orig.clauses)} clauses")
    print(f"  Sym-sub:  {cnf_sym.next_var - 1} vars, "
          f"{len(cnf_sym.clauses)} clauses")


if __name__ == "__main__":
    main()
