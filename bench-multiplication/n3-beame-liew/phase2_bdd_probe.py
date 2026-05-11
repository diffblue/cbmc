#!/usr/bin/env python3
"""
Phase 2 exploration: build BDDs for each output bit c[k] and d[k] of
the array multiplier at small n, verify structural equality
(c[k] = d[k] as BDDs), and report BDD sizes.

This gives a BDD-based equivalence proof as a sanity check that the
CNF is correctly encoding array-multiplier commutativity. It also
provides empirical BDD-size data relevant to the Beame-Liew Phase 2
discussion: Bryant 1991 proved that the BDDs of multiplier outputs
(for input-bit variable orderings) are exponential in n.

Usage: python3 phase2_bdd_probe.py N
"""

import sys
from dd import autoref


def array_multiplier_bdd(n, bdd, a_names, b_names):
    """Build BDDs for each output bit c[0..2n-1] of a_bits * b_bits
    using an array multiplier with ripple-carry full adders.

    Returns: list of 2n BDDs.
    """
    def xor(p, q):
        return bdd.apply('xor', p, q)

    def conj(p, q):
        return bdd.apply('and', p, q)

    def disj(p, q):
        return bdd.apply('or', p, q)

    a = [bdd.var(name) for name in a_names]
    b = [bdd.var(name) for name in b_names]
    # Partial products.
    pp = [[conj(a[i], b[j]) for j in range(n)] for i in range(n)]
    # Initialise accumulator to row 0.
    ZERO = bdd.false
    acc = [ZERO] * (2 * n)
    for j in range(n):
        acc[j] = pp[0][j]
    # Ripple-carry adds row by row.
    for i in range(1, n):
        new_acc = list(acc)
        carry = ZERO
        for j in range(n):
            col = i + j
            x, y, z = acc[col], pp[i][j], carry
            # Full adder: s = x XOR y XOR z; c = maj(x, y, z).
            s = xor(xor(x, y), z)
            co = disj(conj(x, y), disj(conj(x, z), conj(y, z)))
            new_acc[col] = s
            carry = co
        col = i + n
        while col < 2 * n:
            x, y = acc[col], carry
            s = xor(x, y)
            co = conj(x, y)
            new_acc[col] = s
            carry = co
            col += 1
        acc = new_acc
    return acc


def main():
    if len(sys.argv) != 2:
        print("usage: phase2_bdd_probe.py N", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])

    bdd = autoref.BDD()
    # Declare variables. Ordering: interleaved a_i, b_i (often better
    # for arithmetic).
    names = []
    for i in range(n):
        names.extend([f"a{i}", f"b{i}"])
    bdd.declare(*names)

    a_names = [f"a{i}" for i in range(n)]
    b_names = [f"b{i}" for i in range(n)]

    # Build c = a * b.
    print(f"Building BDD for c = a * b (n={n})...", file=sys.stderr)
    c_bdds = array_multiplier_bdd(n, bdd, a_names, b_names)
    c_sizes = [len(bdd) for _ in range(1)]  # placeholder
    # Build d = b * a.
    print(f"Building BDD for d = b * a (n={n})...", file=sys.stderr)
    d_bdds = array_multiplier_bdd(n, bdd, b_names, a_names)

    # Compare per-bit equality.
    n_bdd_nodes = len(bdd)
    print(f"n={n}: total BDD manager size = {n_bdd_nodes} nodes")

    all_equal = True
    for k in range(2 * n):
        # c[k] and d[k] are equivalent iff (c[k] <=> d[k]) is TRUE.
        # In dd.autoref, we can compute XNOR and check against bdd.true.
        eq = bdd.apply('xor', c_bdds[k], d_bdds[k])
        # eq is bdd.false iff c[k] = d[k] for all inputs.
        if eq == bdd.false:
            pass
        else:
            all_equal = False
            print(f"  bit {k}: c[k] != d[k] (not equivalent!)")

    if all_equal:
        print(f"All 2n={2*n} bits: c[k] == d[k] (structural BDD equality) OK")
    else:
        print("SOME BITS DIFFER - BUG")

    # Report BDD sizes per bit (DAG size of each output function).
    for k in range(2 * n):
        size = c_bdds[k].dag_size
        print(f"  bit {k}: c[k] DAG size = {size}")


if __name__ == "__main__":
    main()
