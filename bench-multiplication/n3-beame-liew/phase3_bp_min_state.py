#!/usr/bin/env python3
"""
Phase 3 BP with MINIMAL state merging: only output bits in strip
serve as cut state. This is much more aggressive than cumulative.

Key insight: the BP's path-negation leaves and tree-unfolded emission
don't depend on what state is tracked at cut boundaries, only on the
branch ORDER. So aggressive state merging (fewer distinct states)
produces smaller BP, and tree-unfolding still emits valid DRAT.

Test: does this validate with drat-trim?
"""

import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase3_bp_paper_order import build_strip_all, propagate


def diagonal_branch_order(cnf, k, delta, n):
    strip_cols = list(range(max(0, k - delta), k + 1))
    order = []
    added = set()
    carry_boundary = strip_cols[0] - 1 if strip_cols else -1
    if carry_boundary >= 0:
        for side in ("c", "d"):
            tag = f"cry_{side}"
            for row in range(1, n):
                for v, role in cnf.meta.items():
                    if (role and role[0] == tag and role[1] == row
                            and role[2] == carry_boundary):
                        if v not in added:
                            order.append((-1, v))
                            added.add(v)
                        break
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
    from phase3_bp_cut_v2 import get_output_var_for_col
    for col in strip_cols:
        for side in ("c", "d"):
            ov = get_output_var_for_col(cnf, side, col, n)
            if ov is not None and ov not in added:
                order.append((max(strip_cols) + 1, ov))
                added.add(ov)
    return order


def get_minimal_cut_state(cnf, k, delta, n):
    """Minimal cut state: only OUTPUT bits c[col], d[col] and cry
    vars crossing boundaries."""
    strip_cols = list(range(max(0, k - delta), k + 1))
    state_by_col = defaultdict(set)

    from phase3_bp_cut_v2 import get_output_var_for_col
    for col in strip_cols:
        for side in ("c", "d"):
            ov = get_output_var_for_col(cnf, side, col, n)
            if ov is not None:
                state_by_col[col].add(ov)
        # Also cry vars at col boundary (between col and col+1)
        for side in ("c", "d"):
            for row in range(n):
                for v, role in cnf.meta.items():
                    if (role and role[0] == f"cry_{side}"
                            and role[1] == row and role[2] == col):
                        state_by_col[col].add(v)
                        break
    return state_by_col


def build_bp_minimal(n, k):
    cnf, strip_clauses, forced_e, delta = build_strip_all(n, k)
    branch_order = diagonal_branch_order(cnf, k, delta, n)
    state_by_col = get_minimal_cut_state(cnf, k, delta, n)
    strip_cols = list(range(max(0, k - delta), k + 1))

    init_final, init_conflict = propagate(strip_clauses, forced_e)
    if init_conflict is not None:
        return {"root": None, "nodes": {}, "conflict": init_conflict,
                "flat_order": branch_order}

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

    root_key = (-2, (), 0)
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
                        # Fallback: full state
                        sig = tuple(sorted(
                            (v, new_final[v]) for v in new_final
                            if v not in forced_e))
                    ck = (tag, sig, fp + 1)
                else:
                    # Mid-column, use full assigned state to avoid merging
                    assigned_state = tuple(sorted(
                        (v, new_final[v]) for v in new_final
                        if v not in forced_e))
                    ck = (tag, assigned_state, fp + 1)
                if ck not in nodes:
                    nodes[ck] = None
                    frontier.append((new_final, ck, fp + 1))
                children[bit] = ck
        nodes[key] = {"var": var, "children": children, "flat_pos": fp}
    return {"root": root_key, "nodes": nodes, "flat_order": branch_order}


def emit_tree_post_order(bp, out):
    """Tree-unfolded path-negation emission."""
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
        path.append(var)
        c0 = rec(info["children"][False], path)
        path.pop()
        path.append(-var)
        c1 = rec(info["children"][True], path)
        path.pop()
        if c0 is None or c1 is None:
            return c0 or c1
        if var in c0 and -var in c1:
            res = frozenset((c0 - {var}) | (c1 - {-var}))
        elif -var in c0 and var in c1:
            res = frozenset((c0 - {-var}) | (c1 - {var}))
        elif var not in c0 and -var not in c0:
            res = c0
        elif var not in c1 and -var not in c1:
            res = c1
        else:
            res = frozenset(c0 & c1)
        if res != c0 and res != c1 and res not in emitted:
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


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bp_min_state.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])

    cnf, strip_clauses, forced_e, delta = build_strip_all(n, k)
    bp = build_bp_minimal(n, k)

    cnf_path = f"/tmp/strip_min_n{n}_k{k}.cnf"
    drat_path = f"/tmp/strip_min_n{n}_k{k}.drat"

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

    cnf_b = os.path.getsize(cnf_path)
    drat_b = os.path.getsize(drat_path)
    with open(drat_path) as f:
        lemmas = sum(1 for _ in f)
    nodes = len(bp["nodes"])
    print(f"n={n}, k={k}: BP {nodes} nodes, CNF {cnf_b}B, "
          f"DRAT {drat_b}B ({lemmas} lemmas)")

    import subprocess
    result = subprocess.run(
        ["/tmp/drat-trim", cnf_path, drat_path],
        capture_output=True, text=True, timeout=180,
    )
    for line in result.stdout.split("\n"):
        if line.startswith("s "):
            print(f"  {line}")


if __name__ == "__main__":
    main()
