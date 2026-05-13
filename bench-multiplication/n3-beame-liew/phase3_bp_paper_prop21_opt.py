#!/usr/bin/env python3
"""
Optimized paper-true Prop 2.1 BP construction.

Optimizations over phase3_bp_paper_prop21_true.py:
1. Per-level branching (each level j's branching scoped to that level's vars).
2. Canonical UP order: when multiple unit clauses exist, pick the one whose
   unit variable has smallest ID for determinism.
3. Clause-based hash consing: in addition to structural (var, c0, c1) consing,
   also cons by the resulting clause. Two nodes with same clause (same
   resolution output) share a single BP node.
4. Canonical branching order: sort branching variables by ID for determinism.

The goal is to close the gap between empirical BP size (227k at n=6 k=7)
and paper's theoretical bound (47k = O(k^5 log k)).
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


class OptimizedBP:
    def __init__(self, clauses, var_index, cut_vars_per_level=None):
        self.clauses = clauses
        self.var_index = var_index
        # Sort clauses by (length, smallest |var|) for canonical UP.
        self.sorted_clauses = sorted(
            enumerate(clauses),
            key=lambda pr: (len(pr[1]), min(abs(l) for l in pr[1]) if pr[1] else 0)
        )
        self.nodes = []
        # Structural hash cons
        self.hash_cons = {}
        # Clause-based hash cons
        self.clause_cons = {}
        # Cache of clauses per node (for clause-cons lookup).
        self.node_clause = {}
        # State-based cache: sigma-key -> node_id.
        # Two paths reaching the same sigma produce the same subtree.
        self.state_cache = {}
        # cut_vars_per_level[j] = set of vars in Cut(j+1). When caching
        # state at level j, project sigma to cut vars + branching vars
        # of current and future levels.
        self.cut_vars_per_level = cut_vars_per_level or []

    def _register_node(self, kind, **kwargs):
        """Add a node and return its ID.
        For leaf_conflict: hash cons by axiom.
        For branch: hash cons structurally (var, c0, c1), AND by clause.
        """
        # Remove 'sigma' field from kwargs — not needed post-construction.
        kwargs.pop('sigma', None)

        if kind == 'leaf_conflict':
            axiom = kwargs['axiom']
            key = ('leaf', axiom)
            if key in self.hash_cons:
                return self.hash_cons[key]
            self.nodes.append({'kind': kind, **kwargs})
            nid = len(self.nodes) - 1
            self.hash_cons[key] = nid
            # Leaf's clause = axiom.
            cl = frozenset(axiom)
            self.node_clause[nid] = cl
            self.clause_cons.setdefault(cl, nid)
            return nid

        if kind == 'branch':
            var = kwargs['var']
            c0 = kwargs['c0']
            c1 = kwargs['c1']

            # If both children collapse to same node, skip this branching.
            if c0 == c1:
                return c0

            # Compute clause for this branching.
            cl0 = self.node_clause.get(c0, frozenset())
            cl1 = self.node_clause.get(c1, frozenset())
            if var in cl0 and -var in cl1:
                clause = frozenset((cl0 - {var}) | (cl1 - {-var}))
            elif -var in cl0 and var in cl1:
                clause = frozenset((cl0 - {-var}) | (cl1 - {var}))
            elif var not in cl0 and -var not in cl0:
                clause = cl0
            elif var not in cl1 and -var not in cl1:
                clause = cl1
            else:
                clause = cl0 & cl1

            # Clause-based hash cons: if another node has same clause, reuse.
            if clause in self.clause_cons:
                return self.clause_cons[clause]

            # Structural hash cons.
            skey = ('branch', var, c0, c1)
            if skey in self.hash_cons:
                nid = self.hash_cons[skey]
                return nid

            self.nodes.append({'kind': kind, **kwargs})
            nid = len(self.nodes) - 1
            self.hash_cons[skey] = nid
            self.node_clause[nid] = clause
            self.clause_cons.setdefault(clause, nid)
            return nid

        # Fallback for other kinds.
        self.nodes.append({'kind': kind, **kwargs})
        return len(self.nodes) - 1

    def find_up_step(self, sigma):
        """Find canonical UP step: prefer unit clauses whose unit-var is smallest.
        Also detects conflicts.
        """
        best_unit = None  # (unit_var, val, clause_tuple)
        conflict = None

        # Use var-index for efficient search: for each newly-assigned var,
        # check clauses containing it. But for canonical order, we check
        # all clauses once and find the best unit.
        for clause in self.clauses:
            unassigned = []
            satisfied = False
            for lit in clause:
                v = abs(lit)
                if v in sigma:
                    val_in_sigma = sigma[v]
                    lit_val = val_in_sigma if lit > 0 else not val_in_sigma
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
                if best_unit is None or v < best_unit[0]:
                    best_unit = (v, val, tuple(clause))

        if conflict is not None:
            return ('conflict', conflict)
        if best_unit is not None:
            return ('up', best_unit[0], best_unit[1], best_unit[2])
        return None

    def build(self, sigma, levels, level_idx):
        """Build BP subtree at level `level_idx` starting with `sigma`.

        levels: list of lists of branching vars per level.
        When current level's branching is exhausted and no UP possible,
        move to next level.
        """
        # State-based cache: identical sigmas produce identical subtrees.
        state_key = tuple(sorted(sigma.items()))
        if state_key in self.state_cache:
            return self.state_cache[state_key]

        # Saturate UP at once using propagate_fast with trace.
        trace = []
        final, conflict = propagate_fast(
            self.clauses, sigma, self.var_index, trace=trace
        )

        if conflict is not None:
            # Build UP-as-branching chain: innermost is conflict leaf,
            # then branching nodes for each UP step (in reverse).
            nid = self._register_node(
                'leaf_conflict',
                axiom=tuple(conflict),
            )
            for (var, val, unit_cl) in reversed(trace):
                bad_val = not val
                c_bad = self._register_node(
                    'leaf_conflict',
                    axiom=tuple(unit_cl),
                )
                c_good = nid
                c0 = c_bad if bad_val is False else c_good
                c1 = c_bad if bad_val is True else c_good
                nid = self._register_node('branch', var=var, c0=c0, c1=c1)
            self.state_cache[state_key] = nid
            return nid

        # No conflict. Find next branching var.
        next_var = None
        for lidx in range(level_idx, len(levels)):
            for v in levels[lidx]:
                if v not in final:
                    next_var = v
                    level_idx = lidx
                    break
            if next_var is not None:
                break

        if next_var is None:
            self.nodes.append({'kind': 'stuck'})
            nid = len(self.nodes) - 1
            self.node_clause[nid] = frozenset()
            self.state_cache[state_key] = nid
            return nid

        # Branch on next_var.
        sigma0 = dict(final)
        sigma0[next_var] = False
        sigma1 = dict(final)
        sigma1[next_var] = True
        c0 = self.build(sigma0, levels, level_idx)
        c1 = self.build(sigma1, levels, level_idx)
        branch_nid = self._register_node(
            'branch', var=next_var, c0=c0, c1=c1,
        )

        # Wrap branch_nid with UP-as-branching chain.
        nid = branch_nid
        for (var, val, unit_cl) in reversed(trace):
            bad_val = not val
            c_bad = self._register_node(
                'leaf_conflict',
                axiom=tuple(unit_cl),
            )
            c_good = nid
            c0 = c_bad if bad_val is False else c_good
            c1 = c_bad if bad_val is True else c_good
            nid = self._register_node('branch', var=var, c0=c0, c1=c1)

        self.state_cache[state_key] = nid
        return nid


def compute_clauses(nodes, node_clause_cache):
    """Compute clauses using the pre-computed cache from OptimizedBP."""
    clause_of = dict(node_clause_cache)
    for nid in range(len(nodes)):
        if nid not in clause_of:
            clause_of[nid] = frozenset()
    return clause_of


def emit_drat(nodes, root_id, clause_of, cnf_clauses_set, out):
    emitted = set()
    visited = set()

    def visit(nid):
        if nid in visited:
            return
        visited.add(nid)
        node = nodes[nid]
        if node['kind'] == 'branch':
            visit(node['c0'])
            visit(node['c1'])
        if node['kind'] == 'leaf_conflict':
            return
        cl = clause_of[nid]
        if cl in cnf_clauses_set:
            return
        if cl in emitted:
            return
        emitted.add(cl)
        lits = sorted(cl, key=lambda x: (abs(x), x))
        if lits:
            out.write(' '.join(str(l) for l in lits) + ' 0\n')
        else:
            out.write('0\n')

    visit(root_id)


def build_optimized_bp(n, k):
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

    initial_sigma = {}
    for cl in forced_e_units:
        if len(cl) == 1:
            lit = cl[0]
            initial_sigma[abs(lit)] = lit > 0

    bp = OptimizedBP(clauses, var_index)

    # Per-level branching: use paper's Cut(j) structure.
    levels = []
    for j in range(0, k + 1):
        bv = paper_branch_vars_onesided(j, k, delta, n, role2var)
        # Use paper's order (row-by-row). Sorting is an option but let's
        # try paper's order first.
        levels.append(list(bv))

    root_id = bp.build(initial_sigma, levels, 0)
    return cnf, strip_clauses, bp, root_id


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_paper_prop21_opt.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf, strip_clauses, bp, root_id = build_optimized_bp(n, k)
    print(f"BP nodes: {len(bp.nodes)}")

    clause_of = compute_clauses(bp.nodes, bp.node_clause)

    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    cnf_path = f"/tmp/strip_opt_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_opt_n{n}_k{k}.drat"
    with open(cnf_path, 'w') as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(' '.join(str(l) for l in cl) + ' 0\n')

    cnf_set = set(frozenset(cl) for cl in strip_clauses)
    with open(drat_path, 'w') as f:
        emit_drat(bp.nodes, root_id, clause_of, cnf_set, f)

    cnf_bytes = os.path.getsize(cnf_path)
    drat_bytes = os.path.getsize(drat_path)
    with open(drat_path) as f:
        drat_lines = sum(1 for _ in f)
    print(f"n={n} k={k}: CNF {cnf_bytes}B, DRAT {drat_bytes}B ({drat_lines} lemmas)")

    root_cl = clause_of[root_id]
    print(f"  root clause: {sorted(root_cl) if root_cl else 'EMPTY'} ({len(root_cl)} lits)")

    result = subprocess.run(
        ['/tmp/drat-trim', cnf_path, drat_path],
        capture_output=True, text=True, timeout=300,
    )
    for line in result.stdout.split('\n'):
        if line.startswith('s '):
            print(f"  {line}")


if __name__ == "__main__":
    main()
