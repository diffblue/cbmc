#!/usr/bin/env python3
"""
Paper's Prop 2.1 BP-to-DRAT with LEVEL-AWARE DAG compression.

Structure:
- Level j starts with cut-state sigma_{Cut(j)}. All non-cut UP-derived
  vars in sigma are FORGOTTEN at level boundary (they're implied by
  strip-CNF ∧ sigma_cut).
- Between levels: branching tree (paper's tableau vars) + UP chain.
- At level j+1 boundary: cache node by Cut(j+1) value. Share across
  different level-j starting cut states.

For the resolution proof, this means:
- Each level-j+1 node's clause is ¬sigma_{Cut(j+1)}.
- This clause is derived by resolving away non-cut vars within
  the subtree emanating from a specific level-j cut state.
- When multiple level-j starts reach the same level-j+1 cut state
  via their separate subtrees, they point to the same level-j+1 node
  (DAG merge).

Key trick for DAG validity: when transitioning from one level-j
subtree leaf (full sigma with non-cut vars) to the shared level-j+1
node (labeled by cut_sigma only), we need a RESOLUTION CHAIN that
resolves away non-cut vars. This chain has ONE resolution step per
non-cut var with known value, producing intermediate nodes.
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


class LeveledBP:
    def __init__(self, clauses, var_index, level_info):
        """level_info: list of (cut_vars, branch_vars) per level j.
        cut_vars = Cut(j+1) (what we cache on leaving level j).
        branch_vars = variables to branch on at level j.
        """
        self.clauses = clauses
        self.var_index = var_index
        self.level_info = level_info
        self.nodes = []
        # Cache: (level, cut_sigma_tuple) -> node_id
        self.level_cache = {}

    def new_node(self, **kwargs):
        self.nodes.append(kwargs)
        return len(self.nodes) - 1

    def find_up_step(self, sigma):
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
                return ('conflict', clause)
            if len(unassigned) == 1:
                lit = unassigned[0]
                v = abs(lit)
                val = lit > 0
                return ('up', v, val, clause)
        return None

    def build_level(self, sigma, level_idx):
        """Build BP subtree starting at a node with sigma at given level.
        Within this level: do UP and branching on level's branch_vars.
        When level's branching is exhausted, transition to next level
        via cut-caching.
        """
        if level_idx >= len(self.level_info):
            # No more levels — final state. Just handle UP until conflict.
            return self._build_final(sigma)

        cut_vars, branch_vars = self.level_info[level_idx]

        # UP step first.
        step = self.find_up_step(sigma)
        if step is not None:
            if step[0] == 'conflict':
                _, clause = step
                return self.new_node(
                    kind='leaf_conflict',
                    sigma=dict(sigma),
                    axiom=tuple(clause),
                )
            if step[0] == 'up':
                _, var, val, clause = step
                bad_val = not val
                bad_sigma = dict(sigma)
                bad_sigma[var] = bad_val
                good_sigma = dict(sigma)
                good_sigma[var] = val

                c_bad = self.new_node(
                    kind='leaf_conflict',
                    sigma=bad_sigma,
                    axiom=tuple(clause),
                )
                c_good = self.build_level(good_sigma, level_idx)

                return self.new_node(
                    kind='branch',
                    sigma=dict(sigma),
                    var=var,
                    c0=c_bad if bad_val is False else c_good,
                    c1=c_bad if bad_val is True else c_good,
                )

        # No UP. Find next branching var at this level.
        next_var = None
        for v in branch_vars:
            if v not in sigma:
                next_var = v
                break

        if next_var is None:
            # Branching exhausted. Transition to next level.
            # Project sigma onto Cut(j+1) and cache: shared across
            # subtrees that reach the same cut state.
            cut_sigma = tuple(sorted(
                (v, sigma[v]) for v in cut_vars if v in sigma
            ))
            cache_key = (level_idx + 1, cut_sigma)
            if cache_key in self.level_cache:
                return self.level_cache[cache_key]
            # Restart at next level with ONLY cut_sigma (forget non-cut vars).
            next_sigma = {v: val for v, val in cut_sigma}
            target_id = self.build_level(next_sigma, level_idx + 1)
            self.level_cache[cache_key] = target_id
            return target_id

        # Branch on next_var.
        sigma0 = dict(sigma)
        sigma0[next_var] = False
        sigma1 = dict(sigma)
        sigma1[next_var] = True
        c0 = self.build_level(sigma0, level_idx)
        c1 = self.build_level(sigma1, level_idx)
        return self.new_node(
            kind='branch',
            sigma=dict(sigma),
            var=next_var,
            c0=c0,
            c1=c1,
        )

    def _build_final(self, sigma):
        """Handle final level (beyond last cut)."""
        step = self.find_up_step(sigma)
        if step is None:
            # No progress possible. Shouldn't reach here if strip is UNSAT.
            # Create a dummy conflict via empty clause? Let's mark.
            return self.new_node(
                kind='stuck',
                sigma=dict(sigma),
            )
        if step[0] == 'conflict':
            _, clause = step
            return self.new_node(
                kind='leaf_conflict',
                sigma=dict(sigma),
                axiom=tuple(clause),
            )
        if step[0] == 'up':
            _, var, val, clause = step
            bad_val = not val
            bad_sigma = dict(sigma)
            bad_sigma[var] = bad_val
            good_sigma = dict(sigma)
            good_sigma[var] = val
            c_bad = self.new_node(
                kind='leaf_conflict',
                sigma=bad_sigma,
                axiom=tuple(clause),
            )
            c_good = self._build_final(good_sigma)
            return self.new_node(
                kind='branch',
                sigma=dict(sigma),
                var=var,
                c0=c_bad if bad_val is False else c_good,
                c1=c_bad if bad_val is True else c_good,
            )

    def _build_bridge(self, full_sigma, cut_vars, target_id):
        """Build a chain of resolution nodes bridging from full_sigma
        to target (which has only cut_sigma). Each bridge node resolves
        away one non-cut var.

        Approach: for each non-cut var in full_sigma (not in cut_vars),
        create a 'bridge_branch' node on that var. One child is the
        target (with var forgotten), the other is the "target had var
        with opposite value" which is... the same target? No, that
        wouldn't typecheck.

        Actually, for the resolution proof:
          clause(full_sigma) = ¬full_sigma
          clause(target) = ¬cut_sigma  (shorter)
        
        To DERIVE clause(target) from clauses of full-sigma siblings
        via resolution on non-cut var: we need TWO full-sigma siblings
        that differ by exactly one non-cut var. Their resolution
        eliminates that var.
        
        Problem: we only have ONE full_sigma at this point in the
        recursion. To have two siblings, we'd need to branch on
        non-cut var EARLIER and combine both branches.
        
        SIMPLIFIED APPROACH: instead of bridging via resolution,
        directly set the node to point to target. Then clause(self) =
        clause(target) = ¬cut_sigma. But this means the node LIES
        about its sigma — it has full_sigma but clause is only ¬cut_sigma.
        This is actually consistent with paper's merging where the
        node is LABELED with cut_sigma (forgetting non-cut vars).
        
        For clause computation: the 'bridge' node's clause = ¬cut_sigma
        (directly; it's the same as target).
        
        But then at the parent (branching), resolution on the
        branching var might fail because bridge's clause doesn't
        contain the branching var.
        """
        # Simplified: just return target_id directly (no bridge).
        # This works if the merging structure is such that non-cut vars
        # have been resolved via the branching tree ABOVE this point.
        # Otherwise resolution at ancestors will fail.
        return target_id


def compute_clauses(nodes):
    clause_of = {}
    VISITING = object()

    def post(nid):
        if nid in clause_of:
            cl = clause_of[nid]
            if cl is VISITING:
                raise RuntimeError(f"Cycle at node {nid}")
            return cl
        clause_of[nid] = VISITING
        node = nodes[nid]
        kind = node['kind']

        if kind == 'leaf_conflict':
            cl = frozenset(node['axiom'])
        elif kind == 'stuck':
            cl = frozenset()
        elif kind == 'branch':
            c0 = post(node['c0'])
            c1 = post(node['c1'])
            var = node['var']
            if var in c0 and -var in c1:
                cl = frozenset((c0 - {var}) | (c1 - {-var}))
            elif -var in c0 and var in c1:
                cl = frozenset((c0 - {-var}) | (c1 - {var}))
            elif var not in c0 and -var not in c0:
                cl = c0
            elif var not in c1 and -var not in c1:
                cl = c1
            else:
                cl = c0 & c1
        else:
            cl = frozenset()

        clause_of[nid] = cl
        return cl

    for nid in range(len(nodes)):
        if nid not in clause_of:
            post(nid)
    return clause_of


def emit_drat(nodes, root_id, clause_of, cnf_clauses_set, out):
    emitted = set()

    def visit(nid):
        if nid in emitted:
            return
        emitted.add(nid)
        node = nodes[nid]
        if node['kind'] == 'branch':
            visit(node['c0'])
            visit(node['c1'])
        # Emit after children.
        if node['kind'] == 'leaf_conflict':
            return  # Axiom in CNF.
        cl = clause_of[nid]
        if cl in cnf_clauses_set:
            return  # Already in CNF.
        lits = sorted(cl, key=lambda x: (abs(x), x))
        if lits:
            out.write(' '.join(str(l) for l in lits) + ' 0\n')
        else:
            out.write('0\n')

    visit(root_id)


def build_leveled_bp(n, k):
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

    # Initial sigma (from forced_e units).
    initial_sigma = {}
    for cl in forced_e_units:
        if len(cl) == 1:
            lit = cl[0]
            initial_sigma[abs(lit)] = lit > 0

    # Build level_info.
    level_info = []
    for j in range(0, k + 1):
        cut_vars = paper_cut_onesided(
            j + 1, k, delta, n, role2var, c_bits, d_bits
        )
        branch_vars = paper_branch_vars_onesided(
            j, k, delta, n, role2var
        )
        level_info.append((cut_vars, branch_vars))

    bp = LeveledBP(clauses, var_index, level_info)
    root_id = bp.build_level(initial_sigma, 0)
    return cnf, strip_clauses, bp, root_id


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_paper_dag_true.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf, strip_clauses, bp, root_id = build_leveled_bp(n, k)
    print(f"BP nodes: {len(bp.nodes)}")

    clause_of = compute_clauses(bp.nodes)

    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    cnf_path = f"/tmp/strip_dag_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_dag_n{n}_k{k}.drat"
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
