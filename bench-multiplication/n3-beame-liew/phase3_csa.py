#!/usr/bin/env python3
"""
Phase 3 BP construction, DRAT emission, and full-proof composition
for the CSA multiplier CNF.

This is the CSA counterpart to phase3_bp_diag.py + phase3_bp_diag_drat.py +
phase3_full_diag.py, using the carry-save tableau from
generate_csa_mul_comm_meta.py.

Usage:
  phase3_csa.py strip N K     # build + emit per-strip DRAT, verify
  phase3_csa.py full N        # build + emit full DRAT, verify
  phase3_csa.py bp N K        # just build BP, report size
"""

import math
import os
import sys
import subprocess
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from generate_csa_mul_comm_meta import build_commutativity_csa_cnf


def strip_delta(n):
    return math.ceil(math.log2(max(2 * n, 2)))


def var_col(role):
    """Return column index for role, or None."""
    if role is None:
        return None
    tag = role[0]
    if tag in ("pp_c", "pp_d"):
        return role[1] + role[2]
    if tag in ("d_c", "d_d", "c_c", "c_d"):
        return role[2]
    if tag in ("cpa_c", "cpa_d", "cpa_cry_c", "cpa_cry_d"):
        return role[1]
    if tag == "diff":
        return role[1]
    return None


def extract_strip(cnf, k, delta):
    """Extract phi_Strip(k) from CSA CNF."""
    strip_clauses = []
    for cl in cnf.clauses:
        include = False
        for lit in cl:
            v = abs(lit)
            role = cnf.meta.get(v)
            col = var_col(role)
            if col is not None and k - delta <= col <= k:
                include = True
                break
        if include:
            strip_clauses.append(list(cl))

    # Tableau symmetry pp_c[i,j] = pp_d[j,i].
    pp_c = {}
    pp_d = {}
    for v, role in cnf.meta.items():
        if role is None:
            continue
        if role[0] == "pp_c":
            pp_c[(role[1], role[2])] = v
        elif role[0] == "pp_d":
            pp_d[(role[1], role[2])] = v
    for (i, j), c_var in pp_c.items():
        if k - delta <= i + j <= k:
            d_var = pp_d.get((j, i))
            if d_var is not None:
                strip_clauses.append([-c_var, d_var])
                strip_clauses.append([c_var, -d_var])

    # ZERO constants.
    for v, role in cnf.meta.items():
        if role and role[0] == "zero":
            strip_clauses.append([-v])

    return strip_clauses


def propagate(clauses, assign):
    """UP; returns (final, conflict)."""
    assign = dict(assign)
    changed = True
    while changed:
        changed = False
        for cl in clauses:
            unassigned = []
            satisfied = False
            for lit in cl:
                v = abs(lit)
                if v in assign:
                    val = assign[v] if lit > 0 else not assign[v]
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
                v = abs(lit)
                new_val = lit > 0
                if v in assign and assign[v] != new_val:
                    return assign, cl
                assign[v] = new_val
                changed = True
    return assign, None


def build_strip_all(n, k):
    cnf, a, b, c, d = build_commutativity_csa_cnf(n)
    delta = strip_delta(n)
    strip_clauses = list(extract_strip(cnf, k, delta))
    forced_e = {}
    for v, role in cnf.meta.items():
        if role and role[0] == "diff":
            bit = role[1]
            if bit < k:
                strip_clauses.append([-v])
                forced_e[v] = False
            elif bit == k:
                strip_clauses.append([v])
                forced_e[v] = True
    return cnf, strip_clauses, forced_e, delta, c, d


def diagonal_branch_order(cnf, k, delta, n):
    """Branch order for CSA:
    1. Incoming carries at col strip_start - 1 (c_* vars and cpa_cry_*).
    2. Column-by-column tableau (pp_c); UP derives d_*, c_* via XOR3/MAJ3.
    3. Output cpa_* vars (with cpa_cry_* interleaved per col).
    """
    strip_cols = list(range(max(0, k - delta), k + 1))
    order = []
    added = set()

    # Incoming carries at col strip_start - 1 from outside strip.
    carry_boundary = strip_cols[0] - 1 if strip_cols else -1
    if carry_boundary >= 0:
        for side in ("c", "d"):
            for row in range(n):
                for v, role in cnf.meta.items():
                    if (role and role[0] == f"c_{side}"
                            and role[1] == row
                            and role[2] == carry_boundary):
                        if v not in added:
                            order.append((-1, v))
                            added.add(v)
                        break
        # Include cpa_cry_* at carry_boundary.
        for side in ("c", "d"):
            for v, role in cnf.meta.items():
                if (role and role[0] == f"cpa_cry_{side}"
                        and role[1] == carry_boundary):
                    if v not in added:
                        order.append((-1, v))
                        added.add(v)
                    break

    # Tableau by column (diagonal).
    for col in strip_cols:
        for i in range(max(0, col - n + 1), min(col + 1, n)):
            j = col - i
            if 0 <= j < n:
                for v, role in cnf.meta.items():
                    if (role and role[0] == "pp_c"
                            and role[1] == i and role[2] == j):
                        if v not in added:
                            order.append((col, v))
                            added.add(v)
                        break
        # Include cpa_cry_* and cpa_* at this col for chain propagation.
        for side in ("c", "d"):
            for v, role in cnf.meta.items():
                if (role and role[0] == f"cpa_cry_{side}"
                        and role[1] == col):
                    if v not in added:
                        order.append((col, v))
                        added.add(v)
                    break
        for side in ("c", "d"):
            for v, role in cnf.meta.items():
                if (role and role[0] == f"cpa_{side}"
                        and role[1] == col):
                    if v not in added:
                        order.append((col, v))
                        added.add(v)
                    break

    return order


def get_cut_state_vars(cnf, k, delta, n):
    """Cut(col) = cumulative acc/cry/pp vars for col' <= col in strip."""
    strip_cols = list(range(max(0, k - delta), k + 1))
    state_by_col = defaultdict(set)
    for v, role in cnf.meta.items():
        if not role:
            continue
        tag = role[0]
        if tag in ("d_c", "d_d", "c_c", "c_d"):
            row, col = role[1], role[2]
            if col in strip_cols:
                state_by_col[col].add(v)
        elif tag in ("pp_c", "pp_d"):
            i, j = role[1], role[2]
            col = i + j
            if col in strip_cols:
                state_by_col[col].add(v)
        elif tag in ("cpa_c", "cpa_d", "cpa_cry_c", "cpa_cry_d"):
            col = role[1]
            if col in strip_cols:
                state_by_col[col].add(v)
    return state_by_col


def build_bp_diag(n, k):
    cnf, strip_clauses, forced_e, delta, _, _ = build_strip_all(n, k)
    branch_order = diagonal_branch_order(cnf, k, delta, n)
    state_by_col = get_cut_state_vars(cnf, k, delta, n)
    strip_cols = list(range(max(0, k - delta), k + 1))

    init_final, init_conflict = propagate(strip_clauses, forced_e)
    if init_conflict is not None:
        return cnf, strip_clauses, {
            "root": None, "nodes": {}, "conflict": init_conflict,
            "flat_order": branch_order,
        }

    def cut_sig(assign, up_to_col):
        if up_to_col < 0:
            return ()
        sig = []
        for c in strip_cols:
            if c > up_to_col:
                break
            for v in sorted(state_by_col.get(c, set())):
                if v in forced_e:
                    continue
                if v not in assign:
                    return None
                sig.append((v, assign[v]))
        return tuple(sig)

    root_key = (-2, cut_sig(init_final, -1) or (), 0)
    nodes = {root_key: None}
    frontier = [(init_final, root_key, 0)]

    while frontier:
        assign, key, fp = frontier.pop()
        if nodes.get(key) is not None and "var" in nodes.get(key, {}):
            continue
        while fp < len(branch_order) and branch_order[fp][1] in assign:
            fp += 1
        if fp >= len(branch_order):
            nodes[key] = {"stuck": True}
            continue
        tag, var = branch_order[fp]
        is_last_in_col = (
            fp + 1 >= len(branch_order)
            or branch_order[fp + 1][0] != tag
        )
        children = {}
        for bit in (False, True):
            new_assign = dict(assign)
            new_assign[var] = bit
            new_final, conflict = propagate(strip_clauses, new_assign)
            if conflict is not None:
                leaf_key = ("leaf", tuple(conflict))
                nodes[leaf_key] = {"leaf": list(conflict)}
                children[bit] = leaf_key
            else:
                if is_last_in_col and tag >= 0:
                    sig = cut_sig(new_final, tag)
                    if sig is None:
                        sig = tuple(sorted(
                            (v, new_final[v]) for v in new_final
                            if v not in forced_e))
                    ck = (tag, sig, fp + 1)
                else:
                    assigned_state = tuple(sorted(
                        (v, new_final[v]) for v in new_final
                        if v not in forced_e))
                    ck = (tag, assigned_state, fp + 1)
                if ck not in nodes:
                    nodes[ck] = None
                    frontier.append((new_final, ck, fp + 1))
                children[bit] = ck
        nodes[key] = {"var": var, "children": children, "flat_pos": fp}
    return cnf, strip_clauses, {
        "root": root_key, "nodes": nodes, "flat_order": branch_order,
    }


def emit_tree_post_order(bp, out):
    """Tree-unfolded post-order DRAT emission (path-negation style).

    Each leaf emits the NEGATION OF PATH (branching vars with their
    path values negated). This is RUP-derivable from the violated
    CNF clause + path. Internal nodes emit resolvents on branching
    vars, which works because path literals match the branching vars.
    """
    nodes = bp["nodes"]
    root = bp["root"]
    emitted = set()

    def rec(node_key, path):
        info = nodes.get(node_key)
        if info is None:
            return None
        if "leaf" in info or "stuck" in info:
            cl = frozenset(path)
            if cl and cl not in emitted:
                sorted_lits = sorted(cl, key=lambda x: (abs(x), x))
                out.write(" ".join(str(l) for l in sorted_lits) + " 0\n")
                emitted.add(cl)
            elif not cl and frozenset() not in emitted:
                out.write("0\n")
                emitted.add(frozenset())
            return cl
        var = info["var"]
        path.append(var)  # x=False path: clause contains +x
        c0_cl = rec(info["children"][False], path)
        path.pop()
        path.append(-var)  # x=True path: clause contains -x
        c1_cl = rec(info["children"][True], path)
        path.pop()

        if c0_cl is None or c1_cl is None:
            return c0_cl or c1_cl
        if var in c0_cl and -var in c1_cl:
            res = frozenset((c0_cl - {var}) | (c1_cl - {-var}))
        elif -var in c0_cl and var in c1_cl:
            res = frozenset((c0_cl - {-var}) | (c1_cl - {var}))
        elif var not in c0_cl and -var not in c0_cl:
            res = c0_cl
        elif var not in c1_cl and -var not in c1_cl:
            res = c1_cl
        else:
            res = frozenset(c0_cl & c1_cl)

        if res != c0_cl and res != c1_cl and res not in emitted:
            if res:
                sorted_lits = sorted(res, key=lambda x: (abs(x), x))
                out.write(" ".join(str(l) for l in sorted_lits) + " 0\n")
                emitted.add(res)
            elif not res and frozenset() not in emitted:
                out.write("0\n")
                emitted.add(frozenset())
        return res

    root_cl = rec(root, [])
    if root_cl is not None and not root_cl and frozenset() not in emitted:
        out.write("0\n")
        emitted.add(frozenset())


def emit_strip_drat(n, k, drat_path, cnf_path):
    cnf, strip_clauses, bp = build_bp_diag(n, k)

    max_var = max(abs(l) for cl in strip_clauses for l in cl)
    with open(cnf_path, "w") as f:
        f.write(f"p cnf {max_var} {len(strip_clauses)}\n")
        for cl in strip_clauses:
            f.write(" ".join(str(l) for l in cl) + " 0\n")

    with open(drat_path, "w") as f:
        if bp.get("conflict") is not None:
            f.write("0\n")
        else:
            emit_tree_post_order(bp, f)

    return cnf, bp


def compose_full_proof(n, out_cnf, out_drat):
    """Compose 2n per-strip DRATs into a full commutativity proof."""
    cnf, _, _, delta, c_out, d_out = build_strip_all(n, 0)  # base cnf
    all_clauses = list(cnf.clauses)
    diff_vars = sorted(
        [v for v, r in cnf.meta.items() if r and r[0] == "diff"],
        key=lambda v: cnf.meta[v][1]
    )
    max_var = cnf.next_var - 1
    with open(out_cnf, "w") as f:
        f.write(f"p cnf {max_var} {len(all_clauses)}\n")
        for cl in all_clauses:
            f.write(" ".join(str(l) for l in cl) + " 0\n")

    strip_sizes = []
    with open(out_drat, "w") as out:
        # Tableau symmetry RUP lemmas.
        pp_c_vars = {}
        pp_d_vars = {}
        for v, role in cnf.meta.items():
            if role and role[0] == "pp_c":
                pp_c_vars[(role[1], role[2])] = v
            elif role and role[0] == "pp_d":
                pp_d_vars[(role[1], role[2])] = v
        for (i, j), cv in pp_c_vars.items():
            dv_key = (j, i)
            if dv_key in pp_d_vars:
                dv = pp_d_vars[dv_key]
                if cv == dv:
                    continue
                out.write(f"{-cv} {dv} 0\n")
                out.write(f"{cv} {-dv} 0\n")

        for k in range(0, 2 * n):
            _, strip_clauses, bp = build_bp_diag(n, k)
            extras = set()
            for i, dv in enumerate(diff_vars):
                if i < k:
                    extras.add(dv)
                elif i == k:
                    extras.add(-dv)

            class WeakenedWriter:
                def __init__(self, f, extras):
                    self.f = f
                    self.extras = extras
                    self.count = 0
                def write(self, s):
                    for line in s.split("\n"):
                        line = line.strip()
                        if not line:
                            continue
                        lits = [int(x) for x in line.split()][:-1]
                        weakened = frozenset(lits) | self.extras
                        sorted_lits = sorted(weakened, key=lambda x: (abs(x), x))
                        if sorted_lits:
                            self.f.write(" ".join(str(l) for l in sorted_lits) + " 0\n")
                        else:
                            self.f.write("0\n")
                        self.count += 1

            ww = WeakenedWriter(out, extras)
            if bp.get("conflict") is not None:
                ww.write("0")
            else:
                emit_tree_post_order(bp, ww)
            strip_sizes.append(ww.count)

        for k in range(1, 2 * n):
            out.write(f"{-diff_vars[k]} 0\n")
        out.write("0\n")

    return strip_sizes


def cmd_bp(n, k):
    cnf, strip_clauses, bp = build_bp_diag(n, k)
    if bp.get("conflict"):
        print(f"n={n}, k={k}: UP refutes at root (trivial)")
        return
    total = len(bp["nodes"])
    leaves = sum(1 for i in bp["nodes"].values() if i and "leaf" in i)
    internal = sum(1 for i in bp["nodes"].values() if i and "var" in i)
    stuck = sum(1 for i in bp["nodes"].values() if i and "stuck" in i)
    print(f"n={n}, k={k}: BP {total} nodes "
          f"(int={internal}, leaves={leaves}, stuck={stuck}), "
          f"|bo|={len(bp['flat_order'])}")


def cmd_strip(n, k):
    cnf_path = f"/tmp/csa_strip_n{n}_k{k}.cnf"
    drat_path = f"/tmp/csa_strip_n{n}_k{k}.drat"
    emit_strip_drat(n, k, drat_path, cnf_path)
    cnf_b = os.path.getsize(cnf_path)
    drat_b = os.path.getsize(drat_path)
    with open(drat_path) as f:
        lemmas = sum(1 for _ in f)
    print(f"n={n}, k={k}: CNF {cnf_b}B, DRAT {drat_b}B ({lemmas} lemmas)")
    result = subprocess.run(
        ["/tmp/drat-trim", cnf_path, drat_path],
        capture_output=True, text=True, timeout=180,
    )
    for line in result.stdout.split("\n"):
        if line.startswith("s "):
            print(f"  {line}")


def cmd_full(n):
    cnf_path = f"/tmp/csa_full_n{n}.cnf"
    drat_path = f"/tmp/csa_full_n{n}.drat"
    sizes = compose_full_proof(n, cnf_path, drat_path)
    cnf_b = os.path.getsize(cnf_path)
    drat_b = os.path.getsize(drat_path)
    with open(drat_path) as f:
        lemmas = sum(1 for _ in f)
    print(f"n={n}: CNF {cnf_b}B, DRAT {drat_b}B ({lemmas} lemmas)")
    print(f"  strip sizes: {sizes}")
    result = subprocess.run(
        ["/tmp/drat-trim", cnf_path, drat_path],
        capture_output=True, text=True, timeout=1200,
    )
    for line in result.stdout.split("\n"):
        if line.startswith("s "):
            print(f"  {line}")


def main():
    if len(sys.argv) < 3:
        print(__doc__, file=sys.stderr)
        sys.exit(1)
    cmd = sys.argv[1]
    if cmd == "bp":
        cmd_bp(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "strip":
        cmd_strip(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "full":
        cmd_full(int(sys.argv[2]))
    else:
        print(f"unknown command {cmd}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
