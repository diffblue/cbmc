#!/usr/bin/env python3
"""
Measure BDD sizes for strip variables — gives a lower bound on the
size of the Beame-Liew BP for phi_Strip(k).

For each strip variable (acc_c, acc_d, cry_c, cry_d in strip cols),
build its BDD as a function of a, b. Report total BDD size.
"""

import sys
import os
import math
from dd import autoref

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def strip_delta(n):
    return math.ceil(math.log2(max(2 * n, 2)))


def array_mul_bdds(n, bdd, a_names, b_names):
    """Build BDDs for every intermediate variable of the array
    multiplier a*b. Return a dict (role -> BDD) for roles:
      pp_c[i][j], acc_c[i, col], cry_c[i, col]
    """
    def conj(p, q): return bdd.apply('and', p, q)
    def disj(p, q): return bdd.apply('or', p, q)
    def xor(p, q): return bdd.apply('xor', p, q)

    a = [bdd.var(name) for name in a_names]
    b = [bdd.var(name) for name in b_names]
    roles = {}
    ZERO = bdd.false
    pp = {}
    for i in range(n):
        for j in range(n):
            pp[i, j] = conj(a[i], b[j])
            roles[("pp_c", i, j)] = pp[i, j]
    acc = [ZERO] * (2 * n)
    for j in range(n):
        acc[j] = pp[0, j]
    for i in range(1, n):
        new_acc = list(acc)
        carry = ZERO
        for j in range(n):
            col = i + j
            x = acc[col]; y = pp[i, j]; z = carry
            s = xor(xor(x, y), z)
            co = disj(conj(x, y), disj(conj(x, z), conj(y, z)))
            new_acc[col] = s
            roles[("acc_c", i, col)] = s
            roles[("cry_c", i, col)] = co
            carry = co
        col = i + n
        while col < 2 * n:
            x = acc[col]; y = carry
            s = xor(x, y)
            co = conj(x, y)
            new_acc[col] = s
            roles[("acc_c", i, col)] = s
            roles[("cry_c", i, col)] = co
            carry = co
            col += 1
        acc = new_acc
    # Outputs (= final accumulator).
    for col in range(2 * n):
        roles[("c_out", col)] = acc[col]
    return roles


def strip_bdds_size(n, k):
    bdd = autoref.BDD()
    names = []
    for i in range(n):
        names.extend([f"a{i}", f"b{i}"])
    bdd.declare(*names)

    a_names = [f"a{i}" for i in range(n)]
    b_names = [f"b{i}" for i in range(n)]

    roles_c = array_mul_bdds(n, bdd, a_names, b_names)
    # roles_d: b * a (just swap inputs).
    roles_d_raw = array_mul_bdds(n, bdd, b_names, a_names)
    roles_d = {}
    for (tag, *rest), b_ in roles_d_raw.items():
        new_tag = tag.replace("_c", "_d")
        roles_d[(new_tag, *rest)] = b_
    roles_d["d_out"] = []
    for col in range(2 * n):
        roles_d[("d_out", col)] = roles_d_raw[("c_out", col)]

    all_roles = {}
    all_roles.update(roles_c)
    all_roles.update(roles_d)

    delta = strip_delta(n)
    strip_cols = set(range(max(0, k - delta), k + 1))

    # Report BDD DAG sizes for strip variables.
    per_role_sizes = {}
    for role, bdd_fn in all_roles.items():
        tag = role[0]
        if tag in ("acc_c", "acc_d", "cry_c", "cry_d"):
            col = role[2]
            if col in strip_cols:
                per_role_sizes[role] = bdd_fn.dag_size
        elif tag in ("pp_c", "pp_d"):
            col = role[1] + role[2]
            if col in strip_cols:
                per_role_sizes[role] = bdd_fn.dag_size
        elif tag in ("c_out", "d_out"):
            col = role[1]
            if col in strip_cols:
                per_role_sizes[role] = bdd_fn.dag_size

    total_manager = len(bdd)
    total_strip = sum(per_role_sizes.values())
    return total_manager, total_strip, per_role_sizes


def main():
    if len(sys.argv) != 3:
        print("usage: phase3_bdd_size.py N K", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    k = int(sys.argv[2])
    total_manager, total_strip, per_role = strip_bdds_size(n, k)
    delta = strip_delta(n)
    strip_cols = list(range(max(0, k - delta), k + 1))
    print(f"n={n}, k={k}, strip cols={strip_cols}")
    print(f"Total BDD manager nodes: {total_manager}")
    print(f"Sum of strip-variable DAG sizes: {total_strip} "
          f"(across {len(per_role)} strip vars)")
    if per_role:
        per_role_sizes = sorted(per_role.values(), reverse=True)
        print(f"Top 5 largest strip-var DAG sizes: {per_role_sizes[:5]}")


if __name__ == "__main__":
    main()
