#!/usr/bin/env python3
"""Generate SMT-LIB queries for SABER-style polynomial-multiplication
equivalence at scaled-down N.

We mirror the algorithmic structure of SABER's
Reference_Implementation_KEM/poly_mul.c:

    poly_mul_acc(a, b, res):
        c[2N] = toom_cook_4way(a, b)              # produce 2N-coeff product
        for i in [N, 2N):                         # reduce modulo x^N + 1
            res[i-N] = c[i-N] - c[i]

The reduction step "res[i-N] = c[i-N] - c[i]" reflects the relation
x^N = -1 in the ring R_q = Z_q[x] / (x^N + 1) used by SABER (with
q = 2^13 for the standard parameter set).

We compare two implementations of the polynomial product at level
2N (before reduction):

  - schoolbook:  c[i+j] += a[i] * b[j]   for all i, j in [0, N)
  - karatsuba:   one-level Karatsuba decomposition into halves

Both produce a 2N-coefficient product; we then apply the
"x^N = -1" reduction to get N-coefficient outputs in R_q, and
assert they agree.

This is the universal-equational query
  forall a, b in R_q^N. schoolbook(a, b) == karatsuba(a, b)
which our algebraic procedure should decide.

Usage:
  python make-saber-query.py --n 4 --q 13 > saber-n4-bw13.smt2
  python make-saber-query.py --n 8 --q 13 > saber-n8-bw13.smt2
"""

import argparse
import sys


def emit_query(n: int, qbits: int, algorithm_a: str, algorithm_b: str,
               single_coeff=None):
    """Emit an SMT-LIB query asserting that two polynomial multiplication
    algorithms agree, modulo x^n + 1, with coefficients in Z_{2^qbits}.
    """
    print(f"; SABER-style polynomial multiplication equivalence")
    print(f"; n={n}, q=2^{qbits}, algorithms: {algorithm_a} vs {algorithm_b}")
    print(f"; Mirrors poly_mul_acc() from SABER/Reference_Implementation_KEM/poly_mul.c")
    print(f"; with Toom-Cook 4-way + Karatsuba replaced by simpler decomposition")
    print(f"; suitable for the scaled-down n.")
    print()
    print("(set-logic QF_BV)")
    print()

    # Declare input coefficients
    print(f"; Input: a, b in R_q^{n} where R_q = Z_{{2^{qbits}}}")
    for i in range(n):
        print(f"(declare-const a{i} (_ BitVec {qbits}))")
    for i in range(n):
        print(f"(declare-const b{i} (_ BitVec {qbits}))")
    print()

    def emit_algorithm(name: str, kind: str):
        """Emit the 2n-coefficient product c[0..2n-1] = mul(a, b)."""
        if kind == "schoolbook":
            # c[k] = sum_{i+j=k} a[i] * b[j]   for k in [0, 2n-1)
            print(f"; {name}: schoolbook polynomial multiplication")
            for k in range(2 * n - 1):
                terms = []
                for i in range(n):
                    j = k - i
                    if 0 <= j < n:
                        terms.append(f"(bvmul a{i} b{j})")
                if not terms:
                    expr = f"(_ bv0 {qbits})"
                elif len(terms) == 1:
                    expr = terms[0]
                else:
                    expr = terms[0]
                    for t in terms[1:]:
                        expr = f"(bvadd {expr} {t})"
                print(f"(define-fun {name}_c{k} () (_ BitVec {qbits}) {expr})")
        elif kind == "karatsuba":
            # One-level Karatsuba: split a, b into halves at n/2.
            # a = a_lo + x^{n/2} * a_hi
            # b = b_lo + x^{n/2} * b_hi
            # p1 = a_lo * b_lo            (degree-2*(n/2-1) = n-2 polynomial)
            # p2 = a_hi * b_hi            (likewise)
            # p3 = (a_lo + a_hi) * (b_lo + b_hi) - p1 - p2
            # Final: c = p1 + x^{n/2} * p3 + x^n * p2
            #
            # Since we're scaled down, we use schoolbook for the half-sized
            # multiplications. The contribution of "Karatsuba" here is
            # the structural decomposition which exposes the 3-mul
            # algebraic identity.
            assert n % 2 == 0, "Karatsuba needs even n"
            h = n // 2
            print(f"; {name}: 1-level Karatsuba (halves n={n}/2={h}, schoolbook on halves)")

            # Compute a_lo[i]+a_hi[i] and b_lo[i]+b_hi[i]
            for i in range(h):
                print(f"(define-fun {name}_asum{i} () (_ BitVec {qbits}) (bvadd a{i} a{i + h}))")
                print(f"(define-fun {name}_bsum{i} () (_ BitVec {qbits}) (bvadd b{i} b{i + h}))")

            # p1[k] = sum a_lo[i] * b_lo[j], k = i+j
            for k in range(2 * h - 1):
                terms = []
                for i in range(h):
                    j = k - i
                    if 0 <= j < h:
                        terms.append(f"(bvmul a{i} b{j})")
                expr = terms[0]
                for t in terms[1:]:
                    expr = f"(bvadd {expr} {t})"
                print(f"(define-fun {name}_p1_{k} () (_ BitVec {qbits}) {expr})")

            # p2[k] = sum a_hi[i] * b_hi[j], k = i+j
            for k in range(2 * h - 1):
                terms = []
                for i in range(h):
                    j = k - i
                    if 0 <= j < h:
                        terms.append(f"(bvmul a{i + h} b{j + h})")
                expr = terms[0]
                for t in terms[1:]:
                    expr = f"(bvadd {expr} {t})"
                print(f"(define-fun {name}_p2_{k} () (_ BitVec {qbits}) {expr})")

            # p3[k] = sum asum[i] * bsum[j] - p1[k] - p2[k]
            for k in range(2 * h - 1):
                terms = []
                for i in range(h):
                    j = k - i
                    if 0 <= j < h:
                        terms.append(f"(bvmul {name}_asum{i} {name}_bsum{j})")
                expr = terms[0]
                for t in terms[1:]:
                    expr = f"(bvadd {expr} {t})"
                # p3 = sum - p1 - p2
                expr = f"(bvsub (bvsub {expr} {name}_p1_{k}) {name}_p2_{k})"
                print(f"(define-fun {name}_p3_{k} () (_ BitVec {qbits}) {expr})")

            # c[k] = p1[k] + p3[k - h] + p2[k - n]
            # where indices outside their valid ranges contribute 0.
            for k in range(2 * n - 1):
                terms = []
                if 0 <= k <= 2 * h - 2:
                    terms.append(f"{name}_p1_{k}")
                if 0 <= k - h <= 2 * h - 2:
                    terms.append(f"{name}_p3_{k - h}")
                if 0 <= k - n <= 2 * h - 2:
                    terms.append(f"{name}_p2_{k - n}")
                if not terms:
                    expr = f"(_ bv0 {qbits})"
                elif len(terms) == 1:
                    expr = terms[0]
                else:
                    expr = terms[0]
                    for t in terms[1:]:
                        expr = f"(bvadd {expr} {t})"
                print(f"(define-fun {name}_c{k} () (_ BitVec {qbits}) {expr})")
        elif kind == "karatsuba2":
            # 2-level Karatsuba: outer Karatsuba splits n into 2 halves of
            # h = n/2; each half is itself Karatsuba'd into 2 quarters
            # of q = n/4. Sub-quarter products use schoolbook.
            #
            # This mirrors SABER's "Toom-Cook 4-way + Karatsuba inner"
            # algorithmic structure (multi-level decomposition) at
            # scaled-down n, without requiring extractor support for
            # the Toom-4 shifts (>> 1, >> 3 in SABER's interpolation).
            #
            # Outer: 3 products of h-coefficient polynomials.
            # Inner: each h-product is itself decomposed into 3 products
            #        of q-coefficient polynomials.
            # Total: 9 schoolbook multiplications of q-coefficient
            # polynomials, plus the outer/inner combination layers.
            assert n % 4 == 0, "2-level Karatsuba needs n divisible by 4"
            h = n // 2  # half size
            q = n // 4  # quarter size
            print(f"; {name}: 2-level Karatsuba (n={n} -> halves of {h} -> quarters of {q})")
            print(f"; Outer: 3 h-poly products. Inner: each is 3 q-poly products.")
            print(f"; Total schoolbook q-mults: 9.")

            def one_level_karatsuba(prefix, a_idx_lo, a_idx_hi, b_idx_lo, b_idx_hi, halfsize):
                """Emit code for one-level Karatsuba between two
                half-sized polynomials, using schoolbook on quarters.

                Inputs are accessed via "a{i}" / "b{i}" naming, where
                a_idx_lo[i] and a_idx_hi[i] map index i in [0, halfsize)
                to the actual a-array index. Similarly for b.

                Emits prefix_p1_*, prefix_p2_*, prefix_p3_*, prefix_c*.
                Output: 2*halfsize - 1 coefficients in prefix_c{k}.
                """
                h2 = halfsize // 2
                # asum[i] = a_idx_lo[i] + a_idx_hi[i], etc.
                for i in range(h2):
                    print(f"(define-fun {prefix}_asum{i} () (_ BitVec {qbits}) "
                          f"(bvadd a{a_idx_lo[i]} a{a_idx_hi[i]}))")
                    print(f"(define-fun {prefix}_bsum{i} () (_ BitVec {qbits}) "
                          f"(bvadd b{b_idx_lo[i]} b{b_idx_hi[i]}))")
                # p1: schoolbook on a_idx_lo * b_idx_lo (q quarter * q quarter)
                for k in range(2 * h2 - 1):
                    terms = []
                    for i in range(h2):
                        j = k - i
                        if 0 <= j < h2:
                            terms.append(f"(bvmul a{a_idx_lo[i]} b{b_idx_lo[j]})")
                    expr = terms[0]
                    for t in terms[1:]:
                        expr = f"(bvadd {expr} {t})"
                    print(f"(define-fun {prefix}_p1_{k} () (_ BitVec {qbits}) {expr})")
                # p2: schoolbook on a_idx_hi * b_idx_hi
                for k in range(2 * h2 - 1):
                    terms = []
                    for i in range(h2):
                        j = k - i
                        if 0 <= j < h2:
                            terms.append(f"(bvmul a{a_idx_hi[i]} b{b_idx_hi[j]})")
                    expr = terms[0]
                    for t in terms[1:]:
                        expr = f"(bvadd {expr} {t})"
                    print(f"(define-fun {prefix}_p2_{k} () (_ BitVec {qbits}) {expr})")
                # p3: schoolbook on asum * bsum, minus p1, minus p2
                for k in range(2 * h2 - 1):
                    terms = []
                    for i in range(h2):
                        j = k - i
                        if 0 <= j < h2:
                            terms.append(f"(bvmul {prefix}_asum{i} {prefix}_bsum{j})")
                    expr = terms[0]
                    for t in terms[1:]:
                        expr = f"(bvadd {expr} {t})"
                    expr = f"(bvsub (bvsub {expr} {prefix}_p1_{k}) {prefix}_p2_{k})"
                    print(f"(define-fun {prefix}_p3_{k} () (_ BitVec {qbits}) {expr})")
                # c[k] = p1[k] + p3[k - h2] (shifted by h2) + p2[k - 2*h2]
                for k in range(2 * halfsize - 1):
                    terms = []
                    if 0 <= k <= 2 * h2 - 2:
                        terms.append(f"{prefix}_p1_{k}")
                    if 0 <= k - h2 <= 2 * h2 - 2:
                        terms.append(f"{prefix}_p3_{k - h2}")
                    if 0 <= k - 2 * h2 <= 2 * h2 - 2:
                        terms.append(f"{prefix}_p2_{k - 2 * h2}")
                    if not terms:
                        expr = f"(_ bv0 {qbits})"
                    elif len(terms) == 1:
                        expr = terms[0]
                    else:
                        expr = terms[0]
                        for t in terms[1:]:
                            expr = f"(bvadd {expr} {t})"
                    print(f"(define-fun {prefix}_c{k} () (_ BitVec {qbits}) {expr})")

            # Outer Karatsuba: split a into a_lo (indices 0..h-1) and
            # a_hi (indices h..n-1). Similarly b.
            #
            # Outer p1: a_lo * b_lo  -> inner Karatsuba on quarters
            # Outer p2: a_hi * b_hi  -> inner Karatsuba on quarters
            # Outer p3: (a_lo + a_hi) * (b_lo + b_hi) - p1 - p2

            # Inner-1 (a_lo * b_lo): a_lo split into a[0..q-1] (lower)
            # and a[q..h-1] (upper); same for b.
            print(f"; {name}: inner Karatsuba 1 -- a_lo * b_lo")
            inner1_a_lo = list(range(0, q))
            inner1_a_hi = list(range(q, 2 * q))
            inner1_b_lo = list(range(0, q))
            inner1_b_hi = list(range(q, 2 * q))
            one_level_karatsuba(f"{name}_in1", inner1_a_lo, inner1_a_hi,
                                inner1_b_lo, inner1_b_hi, h)

            # Inner-2 (a_hi * b_hi)
            print(f"; {name}: inner Karatsuba 2 -- a_hi * b_hi")
            inner2_a_lo = list(range(h, h + q))
            inner2_a_hi = list(range(h + q, n))
            inner2_b_lo = list(range(h, h + q))
            inner2_b_hi = list(range(h + q, n))
            one_level_karatsuba(f"{name}_in2", inner2_a_lo, inner2_a_hi,
                                inner2_b_lo, inner2_b_hi, h)

            # Inner-3 ((a_lo + a_hi) * (b_lo + b_hi)) — needs explicit
            # sum variables since indices reference both halves.
            # Define a_outer_sum_i = a[i] + a[i+h] for i in [0, h);
            # similarly for b.
            print(f"; {name}: outer asum / bsum (size {h})")
            for i in range(h):
                print(f"(define-fun {name}_oasum{i} () (_ BitVec {qbits}) (bvadd a{i} a{i + h}))")
                print(f"(define-fun {name}_obsum{i} () (_ BitVec {qbits}) (bvadd b{i} b{i + h}))")

            # Inner-3 uses oasum and obsum, but my one_level_karatsuba
            # helper assumes "a{i}" / "b{i}" indexing — so emit it
            # inline using the sum names.
            print(f"; {name}: inner Karatsuba 3 -- (a_lo + a_hi) * (b_lo + b_hi)")

            def inline_karatsuba(prefix, a_acc, b_acc, halfsize):
                """Like one_level_karatsuba but a_acc(i) / b_acc(i)
                return the SMT-LIB expression to use for the i-th
                element (instead of indexing into a{i}/b{i})."""
                h2 = halfsize // 2
                for i in range(h2):
                    print(f"(define-fun {prefix}_asum{i} () (_ BitVec {qbits}) "
                          f"(bvadd {a_acc(i)} {a_acc(i + h2)}))")
                    print(f"(define-fun {prefix}_bsum{i} () (_ BitVec {qbits}) "
                          f"(bvadd {b_acc(i)} {b_acc(i + h2)}))")
                for k in range(2 * h2 - 1):
                    terms = []
                    for i in range(h2):
                        j = k - i
                        if 0 <= j < h2:
                            terms.append(f"(bvmul {a_acc(i)} {b_acc(j)})")
                    expr = terms[0]
                    for t in terms[1:]:
                        expr = f"(bvadd {expr} {t})"
                    print(f"(define-fun {prefix}_p1_{k} () (_ BitVec {qbits}) {expr})")
                for k in range(2 * h2 - 1):
                    terms = []
                    for i in range(h2):
                        j = k - i
                        if 0 <= j < h2:
                            terms.append(f"(bvmul {a_acc(i + h2)} {b_acc(j + h2)})")
                    expr = terms[0]
                    for t in terms[1:]:
                        expr = f"(bvadd {expr} {t})"
                    print(f"(define-fun {prefix}_p2_{k} () (_ BitVec {qbits}) {expr})")
                for k in range(2 * h2 - 1):
                    terms = []
                    for i in range(h2):
                        j = k - i
                        if 0 <= j < h2:
                            terms.append(f"(bvmul {prefix}_asum{i} {prefix}_bsum{j})")
                    expr = terms[0]
                    for t in terms[1:]:
                        expr = f"(bvadd {expr} {t})"
                    expr = f"(bvsub (bvsub {expr} {prefix}_p1_{k}) {prefix}_p2_{k})"
                    print(f"(define-fun {prefix}_p3_{k} () (_ BitVec {qbits}) {expr})")
                for k in range(2 * halfsize - 1):
                    terms = []
                    if 0 <= k <= 2 * h2 - 2:
                        terms.append(f"{prefix}_p1_{k}")
                    if 0 <= k - h2 <= 2 * h2 - 2:
                        terms.append(f"{prefix}_p3_{k - h2}")
                    if 0 <= k - 2 * h2 <= 2 * h2 - 2:
                        terms.append(f"{prefix}_p2_{k - 2 * h2}")
                    if not terms:
                        expr = f"(_ bv0 {qbits})"
                    elif len(terms) == 1:
                        expr = terms[0]
                    else:
                        expr = terms[0]
                        for t in terms[1:]:
                            expr = f"(bvadd {expr} {t})"
                    print(f"(define-fun {prefix}_c{k} () (_ BitVec {qbits}) {expr})")

            inline_karatsuba(f"{name}_in3",
                             lambda i: f"{name}_oasum{i}",
                             lambda i: f"{name}_obsum{i}",
                             h)

            # Outer combination: p3 = in3 - in1 - in2  (h-half polynomial
            # subtraction, 2h - 1 coefficients).
            print(f"; {name}: outer p3 = in3 - in1 - in2")
            for k in range(2 * h - 1):
                expr = (f"(bvsub (bvsub {name}_in3_c{k} {name}_in1_c{k}) "
                        f"{name}_in2_c{k})")
                print(f"(define-fun {name}_op3_{k} () (_ BitVec {qbits}) {expr})")

            # Final outer: c[k] = in1[k] + op3[k - h] + in2[k - 2h]
            print(f"; {name}: final c[k] = outer Karatsuba combination")
            for k in range(2 * n - 1):
                terms = []
                if 0 <= k <= 2 * h - 2:
                    terms.append(f"{name}_in1_c{k}")
                if 0 <= k - h <= 2 * h - 2:
                    terms.append(f"{name}_op3_{k - h}")
                if 0 <= k - 2 * h <= 2 * h - 2:
                    terms.append(f"{name}_in2_c{k - 2 * h}")
                if not terms:
                    expr = f"(_ bv0 {qbits})"
                elif len(terms) == 1:
                    expr = terms[0]
                else:
                    expr = terms[0]
                    for t in terms[1:]:
                        expr = f"(bvadd {expr} {t})"
                print(f"(define-fun {name}_c{k} () (_ BitVec {qbits}) {expr})")
        else:
            raise ValueError(f"unknown kind {kind}")
        print()

    emit_algorithm("A", algorithm_a)
    emit_algorithm("B", algorithm_b)

    # Both algorithms produce 2n-1 coefficients (c[0..2n-2]); the
    # SABER reduction loop accesses c[i] for i in [n, 2n), which
    # includes c[2n-1]. The high coefficient is implicitly zero
    # since multiplying two degree-(n-1) polynomials gives degree
    # 2n-2. Emit explicit zero definitions for the missing c[2n-1].
    print(f"; High coefficient c[{2 * n - 1}] is zero (implicit; product degree is {2 * n - 2}).")
    print(f"(define-fun A_c{2 * n - 1} () (_ BitVec {qbits}) (_ bv0 {qbits}))")
    print(f"(define-fun B_c{2 * n - 1} () (_ BitVec {qbits}) (_ bv0 {qbits}))")
    print()

    # Reduce modulo x^n + 1: res[i] = c[i] - c[i + n] for i in [0, n)
    print(f"; Reduction modulo x^{n} + 1: res[i] = c[i] - c[i+{n}]")
    print(f"; This mirrors SABER's poly_mul_acc reduction loop.")
    for i in range(n):
        print(f"(define-fun A_res{i} () (_ BitVec {qbits}) "
              f"(bvsub A_c{i} A_c{i + n}))")
        print(f"(define-fun B_res{i} () (_ BitVec {qbits}) "
              f"(bvsub B_c{i} B_c{i + n}))")
    print()

    # Assert disagreement (look for unsat = the implementations agree)
    print("; Disagreement: assert any output coefficient differs.")
    if single_coeff is not None:
        # Test only one specific coefficient — sanity check.
        print(f"; Restricted to coefficient {single_coeff} only.")
        diseq_expr = f"(distinct A_res{single_coeff} B_res{single_coeff})"
    else:
        diseqs = []
        for i in range(n):
            diseqs.append(f"(distinct A_res{i} B_res{i})")
        if len(diseqs) == 1:
            diseq_expr = diseqs[0]
        else:
            diseq_expr = "(or"
            for d in diseqs:
                diseq_expr += f" {d}"
            diseq_expr += ")"
    print(f"(assert {diseq_expr})")
    print("(check-sat)")


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--n", type=int, default=4,
                   help="polynomial degree (number of coefficients)")
    p.add_argument("--q", type=int, default=13,
                   help="bitwidth of each coefficient (q = 2^q)")
    p.add_argument("--algo-a", default="schoolbook",
                   choices=["schoolbook", "karatsuba", "karatsuba2"])
    p.add_argument("--algo-b", default="karatsuba",
                   choices=["schoolbook", "karatsuba", "karatsuba2"])
    p.add_argument("--single-coeff", type=int, default=None,
                   help="if set, assert disagreement on only this output coefficient")
    args = p.parse_args()
    emit_query(args.n, args.q, args.algo_a, args.algo_b,
               single_coeff=args.single_coeff)


if __name__ == "__main__":
    main()
