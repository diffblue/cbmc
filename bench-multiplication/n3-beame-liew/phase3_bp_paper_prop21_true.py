#!/usr/bin/env python3
"""
Paper's exact Prop 2.1 BP-to-DRAT construction.

KEY: each UP step becomes a BRANCHING node (not a single step):
- At node labeled by sigma, we branch on the variable z being derived.
- The z=v_bad child conflicts with some CNF clause C — it is a LEAF with
  clause C (an axiom).
- The z=v_good child continues, labeled by sigma ∪ {z=v_good}.
- The branching node's clause = resolve(axiom C, continuation's clause, z).

This is paper's "propagation" (Figure 3): one child conflicts, the other
is the propagation destination.

Each BP node v has a well-defined maximal clause C_v = ¬sigma_v
(forbidding the partial assignment at v). Each internal node's clause
is a valid resolvent of its children's clauses.

For a TREE-mode BP, emission is straightforward. For DAG, we'll
handle merging in later functions.
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


class PaperBP:
    """Paper's Prop 2.1 BP where each node v has sigma_v and clause
    C_v = ¬sigma_v. UP steps are explicit branching nodes.

    Nodes list: each node is a dict with keys:
      'sigma': dict mapping var -> bool (partial assignment at v)
      'kind': 'leaf_conflict' | 'branch' | 'root'
      For 'leaf_conflict': 'axiom' = CNF clause (tuple of lits)
      For 'branch' / 'root': 'var', 'c0' (child for var=False),
        'c1' (child for var=True)
    """

    def __init__(self, clauses, var_index):
        self.clauses = clauses
        self.var_index = var_index
        self.nodes = []
        # Cache: sigma -> node_id (for deduplication / DAG merge)
        self.sigma_cache = {}
        # Structural hash consing: (kind, var, c0, c1) or (axiom,) -> node_id
        self.hash_cons = {}

    def new_node(self, **kwargs):
        # Hash cons key: only for branch and leaf_conflict.
        kind = kwargs.get('kind')
        if kind == 'leaf_conflict':
            axiom = kwargs.get('axiom')
            key = ('leaf', axiom)
            if key in self.hash_cons:
                return self.hash_cons[key]
            self.nodes.append(kwargs)
            nid = len(self.nodes) - 1
            self.hash_cons[key] = nid
            return nid
        if kind == 'branch':
            var = kwargs.get('var')
            c0 = kwargs.get('c0')
            c1 = kwargs.get('c1')
            # If both children are the same, skip this branch.
            if c0 == c1:
                return c0
            key = ('branch', var, c0, c1)
            if key in self.hash_cons:
                return self.hash_cons[key]
            self.nodes.append(kwargs)
            nid = len(self.nodes) - 1
            self.hash_cons[key] = nid
            return nid
        self.nodes.append(kwargs)
        return len(self.nodes) - 1

    def sigma_key(self, sigma):
        return tuple(sorted(sigma.items()))

    def find_up_step(self, sigma):
        """Find one UP step from sigma.
        Return (var, value, unit_clause) if UP derives var=value,
        or None if no UP step possible (or conflict already).
        Also returns ('conflict', cl) if a clause is already falsified.
        """
        # Check for existing conflict / find unit.
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
                val = lit > 0  # to make lit true
                return ('up', v, val, clause)
        return None

    def build_node(self, sigma, branch_plan, cut_vars, use_cache=False):
        """Build BP rooted at a node labeled by sigma.
        Returns node_id of the created node.

        branch_plan: list of variables to branch on (in order).
          When list is exhausted and UP completes without conflict,
          we reach the "merge boundary" — return a node labeled by
          sigma restricted to cut_vars.
        cut_vars: set of variables that define the "cut state" for
          the next merge.
        use_cache: if True, reuse previously-built subtree with same sigma.
        """
        if use_cache:
            key = self.sigma_key(sigma)
            if key in self.sigma_cache:
                return self.sigma_cache[key]

        # First: handle any UP steps (propagation).
        step = self.find_up_step(sigma)

        if step is not None:
            if step[0] == 'conflict':
                # sigma already falsifies a clause. Leaf.
                _, clause = step
                nid = self.new_node(
                    kind='leaf_conflict',
                    sigma=dict(sigma),
                    axiom=tuple(clause),
                )
                return nid

            if step[0] == 'up':
                _, var, val, clause = step
                # UP step: branching node on var.
                # - child with var=bad_val: leaf with axiom = clause
                # - child with var=val: continuation
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

                c_good = self.build_node(
                    good_sigma, branch_plan, cut_vars, use_cache=use_cache
                )

                nid = self.new_node(
                    kind='branch',
                    sigma=dict(sigma),
                    var=var,
                    c0=c_bad if bad_val is False else c_good,
                    c1=c_bad if bad_val is True else c_good,
                )
                if use_cache:
                    self.sigma_cache[self.sigma_key(sigma)] = nid
                return nid

        # No UP step / conflict. Try a branching step.
        next_var = None
        for v in branch_plan:
            if v not in sigma:
                next_var = v
                break

        if next_var is None:
            # Reached merge boundary. This node represents sigma-at-cut.
            # Its clause is ¬sigma (including all non-cut vars that
            # happen to be in sigma). For DAG merging, we'd resolve
            # away non-cut vars to produce ¬sigma|_cut_vars.
            # For now, tree mode: return a "terminal" node with full sigma.
            nid = self.new_node(
                kind='merge_terminal',
                sigma=dict(sigma),
            )
            return nid

        # Branch on next_var.
        sigma0 = dict(sigma)
        sigma0[next_var] = False
        sigma1 = dict(sigma)
        sigma1[next_var] = True

        c0 = self.build_node(
            sigma0, branch_plan, cut_vars, use_cache=use_cache
        )
        c1 = self.build_node(
            sigma1, branch_plan, cut_vars, use_cache=use_cache
        )

        nid = self.new_node(
            kind='branch',
            sigma=dict(sigma),
            var=next_var,
            c0=c0,
            c1=c1,
        )
        if use_cache:
            self.sigma_cache[self.sigma_key(sigma)] = nid
        return nid


def compute_clauses(nodes):
    """Compute C_v for each node via resolution from leaves.
    - leaf_conflict: C_v = axiom (CNF clause)
    - branch: C_v = resolve(C_{c0}, C_{c1}, var)
    - merge_terminal: C_v = ¬sigma
    """
    clause_of = {}

    def post(nid):
        if nid in clause_of:
            return clause_of[nid]
        node = nodes[nid]
        kind = node['kind']

        if kind == 'leaf_conflict':
            cl = frozenset(node['axiom'])
            clause_of[nid] = cl
            return cl

        if kind == 'merge_terminal':
            # Clause is ¬sigma = {lit s.t. sigma[var]=val means -lit-with-val}
            cl = frozenset(
                -var if val else var
                for var, val in node['sigma'].items()
            )
            clause_of[nid] = cl
            return cl

        if kind == 'branch':
            var = node['var']
            c0 = post(node['c0'])
            c1 = post(node['c1'])
            # c0 (var=0 branch): clause should contain +var (to be falsified
            #   by var=0 which makes +var false).
            # c1 (var=1 branch): clause should contain -var.
            if var in c0 and -var in c1:
                res = frozenset((c0 - {var}) | (c1 - {-var}))
            elif -var in c0 and var in c1:
                # Swapped polarity; shouldn't happen in correct BP but handle.
                res = frozenset((c0 - {-var}) | (c1 - {var}))
            elif var not in c0 and -var not in c0:
                # Child c0 doesn't use var — clause is stronger without var.
                res = c0
            elif var not in c1 and -var not in c1:
                res = c1
            else:
                # Both contain same polarity — fallback to intersection.
                res = c0 & c1

            clause_of[nid] = res
            return res

        clause_of[nid] = frozenset()
        return frozenset()

    for nid in range(len(nodes)):
        post(nid)
    return clause_of


def emit_drat(nodes, root_id, clause_of, cnf_clauses_set, out):
    """Emit DRAT in topological order (leaves first, then internal).
    Skip axiom-leaves (they are in CNF).
    Skip merge_terminal (they're just labels).
    """
    emitted = set()

    def visit(nid):
        if nid in emitted:
            return
        node = nodes[nid]
        # Visit children first.
        if node['kind'] == 'branch':
            visit(node['c0'])
            visit(node['c1'])
        emitted.add(nid)

        if node['kind'] == 'leaf_conflict':
            return  # CNF axiom — already in F
        if node['kind'] == 'merge_terminal':
            # Emit ¬sigma as a RUP lemma (it's trivially RUP because
            # sigma + strip CNF → conflict by BP construction; we rely
            # on the axiom + trivially-falsifying propagation).
            cl = clause_of[nid]
            lits = sorted(cl, key=lambda x: (abs(x), x))
            out.write(' '.join(str(l) for l in lits) + ' 0\n')
            return
        if node['kind'] == 'branch':
            cl = clause_of[nid]
            if cl in cnf_clauses_set:
                return  # Already in CNF
            lits = sorted(cl, key=lambda x: (abs(x), x))
            if lits:
                out.write(' '.join(str(l) for l in lits) + ' 0\n')
            else:
                out.write('0\n')
            return

    visit(root_id)


def build_bp_tree_mode(n, k, use_cache=False):
    """Build BP in tree mode (no DAG merging between levels)."""
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

    # Start with forced_e sigma.
    initial_sigma = {}
    for cl in forced_e_units:
        if len(cl) == 1:
            lit = cl[0]
            initial_sigma[abs(lit)] = lit > 0

    bp = PaperBP(clauses, var_index)

    # Collect ALL branching vars across all levels (paper: tableau vars
    # + carries). For simplicity, concatenate per-level branch vars.
    all_branch_vars = []
    for j in range(0, k + 1):
        branch_vars = paper_branch_vars_onesided(j, k, delta, n, role2var)
        for v in branch_vars:
            if v not in all_branch_vars:
                all_branch_vars.append(v)

    root_id = bp.build_node(
        initial_sigma, all_branch_vars, cut_vars=set(), use_cache=use_cache
    )

    return cnf, strip_clauses, bp, root_id


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_paper_prop21_true.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    # Use caching (use_cache=True) for DAG compression.
    use_cache = os.environ.get("USE_CACHE", "1") == "1"

    cnf, strip_clauses, bp, root_id = build_bp_tree_mode(n, k, use_cache=use_cache)

    print(f"BP nodes: {len(bp.nodes)} (cache={'on' if use_cache else 'off'})")

    clause_of = compute_clauses(bp.nodes)

    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    cnf_path = f"/tmp/strip_prop21_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_prop21_n{n}_k{k}.drat"

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
