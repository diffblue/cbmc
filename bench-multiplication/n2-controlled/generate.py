#!/usr/bin/env python3
"""
N2 controlled experiment benchmark generator.

Produces paired SMT-LIB benchmarks for isolating carry propagation as
the SAT hardness driver in multiplication. All variants share the same
partial-product layout and accumulation topology; only the accumulator
operator changes.

Variants:
  E0_int_seq: integer shift-add (sequential ripple-add accumulation)
  E1_gf2_seq: GF(2) shift-add (sequential bvxor accumulation)
  E2_int_par: integer Wallace-tree-like (parallel CSA accumulation)
  E3_gf2_par: GF(2) Wallace-tree-like (parallel bvxor accumulation)
  E4_int_ternary: integer 3-input sum-chain (more carry propagation)

Each benchmark asserts commutativity: P(a,b) = P(b,a).

Key causal comparisons:
  C1 (parallelness, integer): E0 vs E2
  C2 (parallelness, GF(2)): E1 vs E3
  C3 (carry presence, sequential): E0 vs E1  <- primary causation test
  C4 (carry depth, integer sequential): E0 vs E4
  C5 (carry presence, parallel): E2 vs E3
"""

import os
import sys

HEADER = """(set-logic QF_BV)
; N2 controlled experiment benchmark.
; Pattern: {pattern}, variant: {variant}, bitwidth: {bw}
(declare-fun a () (_ BitVec {bw}))
(declare-fun b () (_ BitVec {bw}))
"""

def bvop(op, x, y):
    return f"(bv{op} {x} {y})"

def bvextract(hi, lo, x):
    return f"((_ extract {hi} {lo}) {x})"

def bvshl(x, n, bw):
    if n == 0:
        return x
    return f"(bvshl {x} (_ bv{n} {bw}))"

def bvconcat(x, y):
    return f"(concat {x} {y})"

def bvzero(n):
    return f"(_ bv0 {n})"

def bvand(x, y):
    return bvop("and", x, y)

def bvadd(x, y):
    return bvop("add", x, y)

def bvxor(x, y):
    return bvop("xor", x, y)

def partial_product(a, b_bit_mask, bw, shift):
    """Compute partial product: (a if b_bit else 0) << shift, as 2N-bit BV."""
    # Zero-extend a to 2N bits
    a_ext = f"((_ zero_extend {bw}) {a})"
    # Select: (b_bit_mask & ...) gives a if bit set else 0
    # We use (bvand (concat 0...0, mask) a_ext)
    masked = bvand(b_bit_mask, a_ext)
    return bvshl(masked, shift, 2*bw)

def mask_from_bit(b, i, bw):
    """Mask replicating bit i of b to 2*bw bits."""
    # Extract bit i, sign-extend to 2*bw (giving all 0s or all 1s)
    bit = bvextract(i, i, b)
    return f"((_ sign_extend {2*bw-1}) {bit})"

def integer_seq_mul(a, b, bw):
    """Sequential shift-add multiplication: ((...((pp0+pp1)+pp2)+pp3)+...)"""
    pps = []
    for i in range(bw):
        m = mask_from_bit(b, i, bw)
        pp = partial_product(a, m, bw, i)
        pps.append(pp)
    # Fold left: ripple chain of adds
    acc = pps[0]
    for pp in pps[1:]:
        acc = bvadd(acc, pp)
    return acc

def gf2_seq_mul(a, b, bw):
    """Sequential GF(2) mul: same partial products, XOR accumulation."""
    pps = []
    for i in range(bw):
        m = mask_from_bit(b, i, bw)
        pp = partial_product(a, m, bw, i)
        pps.append(pp)
    acc = pps[0]
    for pp in pps[1:]:
        acc = bvxor(acc, pp)
    return acc

def tree_fold(pps, op):
    """Parallel tree-fold: log-depth balanced reduction."""
    while len(pps) > 1:
        next_pps = []
        for i in range(0, len(pps) - 1, 2):
            next_pps.append(op(pps[i], pps[i+1]))
        if len(pps) % 2 == 1:
            next_pps.append(pps[-1])
        pps = next_pps
    return pps[0]

def integer_par_mul(a, b, bw):
    """Parallel-tree integer mul: balanced bvadd reduction."""
    pps = []
    for i in range(bw):
        m = mask_from_bit(b, i, bw)
        pp = partial_product(a, m, bw, i)
        pps.append(pp)
    return tree_fold(pps, bvadd)

def gf2_par_mul(a, b, bw):
    """Parallel-tree GF(2) mul: balanced bvxor reduction."""
    pps = []
    for i in range(bw):
        m = mask_from_bit(b, i, bw)
        pp = partial_product(a, m, bw, i)
        pps.append(pp)
    return tree_fold(pps, bvxor)

def bv3add(x, y, z, bw):
    """3-input add via nested bvadd (the SAT solver sees 3-input carry)."""
    return bvadd(bvadd(x, y), z)

def integer_ternary_mul(a, b, bw):
    """Sequential mul with 3-input add grouping: more carry propagation per step."""
    pps = []
    for i in range(bw):
        m = mask_from_bit(b, i, bw)
        pp = partial_product(a, m, bw, i)
        pps.append(pp)
    # Group 3-at-a-time with 3-input add chain
    i = 0
    acc = pps[0]
    i = 1
    while i < len(pps):
        if i + 1 < len(pps):
            acc = bv3add(acc, pps[i], pps[i+1], bw)
            i += 2
        else:
            acc = bvadd(acc, pps[i])
            i += 1
    return acc

VARIANTS = {
    "E0_int_seq": integer_seq_mul,
    "E1_gf2_seq": gf2_seq_mul,
    "E2_int_par": integer_par_mul,
    "E3_gf2_par": gf2_par_mul,
    "E4_int_ternary": integer_ternary_mul,
}

def make_commutativity(variant, bw):
    mulfn = VARIANTS[variant]
    prod_ab = mulfn("a", "b", bw)
    prod_ba = mulfn("b", "a", bw)
    smt = HEADER.format(pattern="commutativity", variant=variant, bw=bw)
    smt += f"(define-fun prod_ab () (_ BitVec {2*bw}) {prod_ab})\n"
    smt += f"(define-fun prod_ba () (_ BitVec {2*bw}) {prod_ba})\n"
    smt += "(assert (not (= prod_ab prod_ba)))\n"
    smt += "(check-sat)\n(exit)\n"
    return smt

def main():
    outdir = os.path.dirname(os.path.abspath(__file__))
    bitwidths = [6, 8, 10, 12, 14, 16]
    for variant in VARIANTS:
        for bw in bitwidths:
            smt = make_commutativity(variant, bw)
            fname = os.path.join(outdir, f"{variant}_comm_{bw}.smt2")
            with open(fname, "w") as f:
                f.write(smt)
            print(f"wrote {fname}")

if __name__ == "__main__":
    main()
