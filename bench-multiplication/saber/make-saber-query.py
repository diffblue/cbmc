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
               single_coeff=None, cmp_qbits=None):
    """Emit an SMT-LIB query asserting that two polynomial multiplication
    algorithms agree, modulo x^n + 1, with coefficients in Z_{2^qbits}.

    cmp_qbits, if set and < qbits, narrows the comparison to the low
    cmp_qbits bits of each output coefficient — i.e., the algorithms
    must agree modulo 2^cmp_qbits. This is needed for faithful SABER
    Toom-Cook 4-way verification: SABER's algorithm is correct modulo
    q = 2^13 but NOT mod 2^16 (the storage type uint16_t). With
    cmp_qbits = 13, we get UNSAT for the toom4 vs schoolbook query
    over arbitrary uint16 inputs.
    """
    if cmp_qbits is None:
        cmp_qbits = qbits
    print(f"; SABER-style polynomial multiplication equivalence")
    print(f"; n={n}, q=2^{qbits}, algorithms: {algorithm_a} vs {algorithm_b}")
    if cmp_qbits != qbits:
        print(f"; comparison modulo 2^{cmp_qbits} (low {cmp_qbits} bits)")
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
        elif kind == "toom4":
            # Faithful Toom-Cook 4-way as in SABER's
            # Reference_Implementation_KEM/poly_mul.c. Splits each
            # input polynomial into 4 sub-polys of size N_SB = n/4,
            # evaluates at 7 points (0, 1, -1, 2, scaled-1/2,
            # scaled--1/2, infinity), multiplies pointwise as
            # polynomials (giving 2*N_SB-1 coefficients each),
            # interpolates back into 7 chunks placed at offsets
            # 0, N_SB, 2*N_SB, ..., 6*N_SB.
            #
            # The interpolation uses bvshl (=*2^k) and bvlshr
            # (=/2^k, exact in this context by construction) and
            # multiplication by the modular inverses inv3=43691,
            # inv9=36409, inv15=61167 in Z_{2^16}. Hence q must be
            # 16 (else the inverses don't apply).
            #
            # Inner products use schoolbook (we already verify
            # schoolbook = karatsuba elsewhere).
            if n % 4 != 0:
                raise ValueError(
                    "Toom-Cook 4-way needs n divisible by 4")
            if n < 4:
                raise ValueError(
                    "Toom-Cook 4-way needs n >= 8 (so N_SB >= 2)")
            if qbits != 16:
                raise ValueError(
                    "Toom-Cook 4-way is hard-coded for q=16 "
                    "(uses inv3=43691, inv9=36409, inv15=61167 in "
                    "Z_{2^16})")
            N_SB = n // 4
            N_SB_RES = 2 * N_SB - 1
            inv3 = 43691
            inv9 = 36409
            inv15 = 61167
            print(f"; {name}: Toom-Cook 4-way (faithful to SABER's "
                  f"poly_mul.c)")
            print(f"; n={n}, N_SB={N_SB}, N_SB_RES={N_SB_RES}, q=16; "
                  f"inv3={inv3}, inv9={inv9}, inv15={inv15}")

            def shift(amt):
                return f"(_ bv{amt} 16)"

            def addn(*xs):
                """Left-associated bvadd."""
                if not xs:
                    return "(_ bv0 16)"
                expr = xs[0]
                for x in xs[1:]:
                    expr = f"(bvadd {expr} {x})"
                return expr

            # Evaluation phase (a-side): for each j in [0, N_SB),
            # define aw1..aw7[j] as polynomials in a[*].
            #
            # Naming: a-coefficients are a{k*N_SB + j} for k in 0..3
            # (which is the "k-th sub-poly evaluated at j").
            print(f"; {name}: evaluation phase (a-side)")
            for j in range(N_SB):
                a0 = f"a{0 * N_SB + j}"
                a1 = f"a{1 * N_SB + j}"
                a2 = f"a{2 * N_SB + j}"
                a3 = f"a{3 * N_SB + j}"
                # aw1[j] = A3[j]
                print(f"(define-fun {name}_aw1_{j} () (_ BitVec 16) "
                      f"{a3})")
                # aw2[j] = (a3<<3) + (a2<<2) + (a1<<1) + a0
                print(f"(define-fun {name}_aw2_{j} () (_ BitVec 16) "
                      f"{addn(f'(bvshl {a3} {shift(3)})',
                              f'(bvshl {a2} {shift(2)})',
                              f'(bvshl {a1} {shift(1)})',
                              a0)})")
                # aw3[j] = a0 + a1 + a2 + a3
                print(f"(define-fun {name}_aw3_{j} () (_ BitVec 16) "
                      f"{addn(a0, a1, a2, a3)})")
                # aw4[j] = (a0 + a2) - (a1 + a3)
                print(f"(define-fun {name}_aw4_{j} () (_ BitVec 16) "
                      f"(bvsub (bvadd {a0} {a2}) (bvadd {a1} {a3})))")
                # aw5[j] = ((a0<<2) + a2) << 1 + ((a1<<2) + a3)
                #        = 8*a0 + 4*a1 + 2*a2 + a3
                print(f"(define-fun {name}_aw5_{j} () (_ BitVec 16) "
                      f"(bvadd "
                      f"(bvshl (bvadd (bvshl {a0} {shift(2)}) {a2}) "
                      f"{shift(1)}) "
                      f"(bvadd (bvshl {a1} {shift(2)}) {a3})))")
                # aw6[j] = ((a0<<2) + a2) << 1 - ((a1<<2) + a3)
                #        = 8*a0 - 4*a1 + 2*a2 - a3
                print(f"(define-fun {name}_aw6_{j} () (_ BitVec 16) "
                      f"(bvsub "
                      f"(bvshl (bvadd (bvshl {a0} {shift(2)}) {a2}) "
                      f"{shift(1)}) "
                      f"(bvadd (bvshl {a1} {shift(2)}) {a3})))")
                # aw7[j] = A0[j]
                print(f"(define-fun {name}_aw7_{j} () (_ BitVec 16) "
                      f"{a0})")

            # Evaluation phase (b-side): same structure.
            print(f"; {name}: evaluation phase (b-side)")
            for j in range(N_SB):
                b0 = f"b{0 * N_SB + j}"
                b1 = f"b{1 * N_SB + j}"
                b2 = f"b{2 * N_SB + j}"
                b3 = f"b{3 * N_SB + j}"
                print(f"(define-fun {name}_bw1_{j} () (_ BitVec 16) "
                      f"{b3})")
                print(f"(define-fun {name}_bw2_{j} () (_ BitVec 16) "
                      f"{addn(f'(bvshl {b3} {shift(3)})',
                              f'(bvshl {b2} {shift(2)})',
                              f'(bvshl {b1} {shift(1)})',
                              b0)})")
                print(f"(define-fun {name}_bw3_{j} () (_ BitVec 16) "
                      f"{addn(b0, b1, b2, b3)})")
                print(f"(define-fun {name}_bw4_{j} () (_ BitVec 16) "
                      f"(bvsub (bvadd {b0} {b2}) (bvadd {b1} {b3})))")
                print(f"(define-fun {name}_bw5_{j} () (_ BitVec 16) "
                      f"(bvadd "
                      f"(bvshl (bvadd (bvshl {b0} {shift(2)}) {b2}) "
                      f"{shift(1)}) "
                      f"(bvadd (bvshl {b1} {shift(2)}) {b3})))")
                print(f"(define-fun {name}_bw6_{j} () (_ BitVec 16) "
                      f"(bvsub "
                      f"(bvshl (bvadd (bvshl {b0} {shift(2)}) {b2}) "
                      f"{shift(1)}) "
                      f"(bvadd (bvshl {b1} {shift(2)}) {b3})))")
                print(f"(define-fun {name}_bw7_{j} () (_ BitVec 16) "
                      f"{b0})")

            # Inner products: w_k[i] = sum aw_k[j] * bw_k[i-j] for
            # j in [0, N_SB), where 0 <= i-j < N_SB. Uses schoolbook
            # since we verify schoolbook = karatsuba elsewhere.
            print(f"; {name}: inner products w_k[i] = aw_k * bw_k "
                  f"(schoolbook), {2 * N_SB - 1} coefficients each")
            for w_idx in range(1, 8):
                for i in range(N_SB_RES):
                    terms = []
                    for j in range(N_SB):
                        jj = i - j
                        if 0 <= jj < N_SB:
                            terms.append(
                                f"(bvmul {name}_aw{w_idx}_{j} "
                                f"{name}_bw{w_idx}_{jj})")
                    expr = addn(*terms)
                    print(f"(define-fun {name}_w{w_idx}_{i} () "
                          f"(_ BitVec 16) {expr})")

            # Interpolation: per i in [0, N_SB_RES), apply the C code's
            # transform to (w1[i], w2[i], ..., w7[i]) yielding the 7
            # values placed at C[i + 0*N_SB] through C[i + 6*N_SB].
            #
            # C code (renamed s_i for SSA clarity):
            #   r0 = w1[i]; r1 = w2[i]; r2 = w3[i]; r3 = w4[i]
            #   r4 = w5[i]; r5 = w6[i]; r6 = w7[i]
            #   s_r1_a = r1 + r4
            #   s_r5_a = r5 - r4
            #   s_r3_a = (r3 - r2) >> 1
            #   s_r4_a = r4 - r0 - (r6 << 6)
            #   s_r4_b = (s_r4_a << 1) + s_r5_a
            #   s_r2_a = r2 + s_r3_a
            #   s_r1_b = s_r1_a - (s_r2_a << 6) - s_r2_a
            #   s_r2_b = s_r2_a - r6 - r0
            #   s_r1_c = s_r1_b + 45 * s_r2_b
            #   s_r4_c = ((s_r4_b - (s_r2_b << 3)) * inv3) >> 3
            #   s_r5_b = s_r5_a + s_r1_c
            #   s_r1_d = ((s_r1_c + (s_r3_a << 4)) * inv9) >> 1
            #   s_r3_b = -(s_r3_a + s_r1_d)
            #   s_r5_c = ((30 * s_r1_d - s_r5_b) * inv15) >> 2
            #   s_r2_c = s_r2_b - s_r4_c
            #   s_r1_e = s_r1_d - s_r5_c
            #
            # Final outputs (which become contributions to C):
            #   chunk 0 (offset 0)        : r6  (= w7[i])
            #   chunk 1 (offset N_SB)     : s_r5_c
            #   chunk 2 (offset 2*N_SB)   : s_r4_c
            #   chunk 3 (offset 3*N_SB)   : s_r3_b
            #   chunk 4 (offset 4*N_SB)   : s_r2_c
            #   chunk 5 (offset 5*N_SB)   : s_r1_e
            #   chunk 6 (offset 6*N_SB)   : r0  (= w1[i])
            print(f"; {name}: interpolation phase (per i)")
            # The SABER C interpolation uses C's int promotion: uint16
            # operands get zero-extended to int (32-bit), then operations
            # happen in int, then truncated back to uint16. For shifts
            # this matters because:
            #   - `(r3 - r2) >> 1`: int subtraction can produce values
            #     where the 17th bit (bit 16 of the 32-bit int) matters
            #     for the arithmetic shift result.
            #   - `((... ) * (uint32_t)inv3) >> 3`: cast to uint32_t for
            #     the multiplication, then logical shift in 32-bit.
            # We model these by zero-extending to 32-bit, doing the
            # operation in 32-bit BV, and extracting low 16 bits.
            # Other operations (bvadd, bvsub, bvmul, bvshl with no
            # subsequent shift) only depend on low 16 bits of the result
            # so we keep them in 16-bit.
            def ext(x16):
                return f"((_ zero_extend 16) {x16})"

            def trunc(x32):
                return f"((_ extract 15 0) {x32})"
            for i in range(N_SB_RES):
                r0 = f"{name}_w1_{i}"
                r1 = f"{name}_w2_{i}"
                r2 = f"{name}_w3_{i}"
                r3 = f"{name}_w4_{i}"
                r4 = f"{name}_w5_{i}"
                r5 = f"{name}_w6_{i}"
                r6 = f"{name}_w7_{i}"

                def lvar(n_):
                    return f"{name}_int_{n_}_{i}"

                # s_r1_a = r1 + r4 (16-bit, mod 2^16)
                print(f"(define-fun {lvar('s_r1_a')} () (_ BitVec 16) "
                      f"(bvadd {r1} {r4}))")
                # s_r5_a = r5 - r4
                print(f"(define-fun {lvar('s_r5_a')} () (_ BitVec 16) "
                      f"(bvsub {r5} {r4}))")
                # s_r3_a = ((r3 - r2) >> 1) in 32-bit-int semantics:
                # zero-extend then bvashr (arithmetic shift on the 32-bit
                # signed value).
                print(f"(define-fun {lvar('s_r3_a')} () (_ BitVec 16) "
                      f"{trunc(f'(bvashr (bvsub {ext(r3)} {ext(r2)}) (_ bv1 32))')})")
                # s_r4_a = r4 - r0 - (r6 << 6)  (16-bit)
                print(f"(define-fun {lvar('s_r4_a')} () (_ BitVec 16) "
                      f"(bvsub (bvsub {r4} {r0}) "
                      f"(bvshl {r6} {shift(6)})))")
                # s_r4_b = (s_r4_a << 1) + s_r5_a  (16-bit)
                print(f"(define-fun {lvar('s_r4_b')} () (_ BitVec 16) "
                      f"(bvadd (bvshl {lvar('s_r4_a')} {shift(1)}) "
                      f"{lvar('s_r5_a')}))")
                # s_r2_a = r2 + s_r3_a
                print(f"(define-fun {lvar('s_r2_a')} () (_ BitVec 16) "
                      f"(bvadd {r2} {lvar('s_r3_a')}))")
                # s_r1_b = s_r1_a - (s_r2_a << 6) - s_r2_a
                print(f"(define-fun {lvar('s_r1_b')} () (_ BitVec 16) "
                      f"(bvsub (bvsub {lvar('s_r1_a')} "
                      f"(bvshl {lvar('s_r2_a')} {shift(6)})) "
                      f"{lvar('s_r2_a')}))")
                # s_r2_b = s_r2_a - r6 - r0
                print(f"(define-fun {lvar('s_r2_b')} () (_ BitVec 16) "
                      f"(bvsub (bvsub {lvar('s_r2_a')} {r6}) {r0}))")
                # s_r1_c = s_r1_b + 45 * s_r2_b
                print(f"(define-fun {lvar('s_r1_c')} () (_ BitVec 16) "
                      f"(bvadd {lvar('s_r1_b')} "
                      f"(bvmul (_ bv45 16) {lvar('s_r2_b')})))")
                # s_r4_c = ((s_r4_b - (s_r2_b << 3)) * inv3) >> 3
                # The cast to uint32_t in C makes this 32-bit
                # multiplication, then logical right shift 3.
                inner_4c = (
                    f"(bvsub {ext(lvar('s_r4_b'))} "
                    f"(bvshl {ext(lvar('s_r2_b'))} (_ bv3 32)))"
                )
                expr_4c = (
                    f"(bvlshr (bvmul {inner_4c} (_ bv{inv3} 32)) "
                    f"(_ bv3 32))"
                )
                print(f"(define-fun {lvar('s_r4_c')} () (_ BitVec 16) "
                      f"{trunc(expr_4c)})")
                # s_r5_b = s_r5_a + s_r1_c (16-bit)
                print(f"(define-fun {lvar('s_r5_b')} () (_ BitVec 16) "
                      f"(bvadd {lvar('s_r5_a')} {lvar('s_r1_c')}))")
                # s_r1_d = ((s_r1_c + (s_r3_a << 4)) * inv9) >> 1
                # 32-bit semantics, logical shift.
                inner_1d = (
                    f"(bvadd {ext(lvar('s_r1_c'))} "
                    f"(bvshl {ext(lvar('s_r3_a'))} (_ bv4 32)))"
                )
                expr_1d = (
                    f"(bvlshr (bvmul {inner_1d} (_ bv{inv9} 32)) "
                    f"(_ bv1 32))"
                )
                print(f"(define-fun {lvar('s_r1_d')} () (_ BitVec 16) "
                      f"{trunc(expr_1d)})")
                # s_r3_b = -(s_r3_a + s_r1_d)
                print(f"(define-fun {lvar('s_r3_b')} () (_ BitVec 16) "
                      f"(bvneg (bvadd {lvar('s_r3_a')} "
                      f"{lvar('s_r1_d')})))")
                # s_r5_c = ((30 * s_r1_d - s_r5_b) * inv15) >> 2
                # 32-bit semantics, logical shift.
                inner_5c = (
                    f"(bvsub "
                    f"(bvmul (_ bv30 32) {ext(lvar('s_r1_d'))}) "
                    f"{ext(lvar('s_r5_b'))})"
                )
                expr_5c = (
                    f"(bvlshr (bvmul {inner_5c} (_ bv{inv15} 32)) "
                    f"(_ bv2 32))"
                )
                print(f"(define-fun {lvar('s_r5_c')} () (_ BitVec 16) "
                      f"{trunc(expr_5c)})")
                # s_r2_c = s_r2_b - s_r4_c
                print(f"(define-fun {lvar('s_r2_c')} () (_ BitVec 16) "
                      f"(bvsub {lvar('s_r2_b')} {lvar('s_r4_c')}))")
                # s_r1_e = s_r1_d - s_r5_c
                print(f"(define-fun {lvar('s_r1_e')} () (_ BitVec 16) "
                      f"(bvsub {lvar('s_r1_d')} {lvar('s_r5_c')}))")

            # Final c[k]: sum of contributions from the 7 chunks.
            # chunk c (c in 0..6) at offset c*N_SB contributes
            # value out_c[i] for i = k - c*N_SB if 0 <= i < N_SB_RES.
            #
            # out values per chunk:
            #   chunk 0: w7[i]                 (r6)
            #   chunk 1: s_r5_c
            #   chunk 2: s_r4_c
            #   chunk 3: s_r3_b
            #   chunk 4: s_r2_c
            #   chunk 5: s_r1_e
            #   chunk 6: w1[i]                 (r0)
            chunk_value = [
                lambda i: f"{name}_w7_{i}",       # chunk 0 = r6
                lambda i: f"{name}_int_s_r5_c_{i}",
                lambda i: f"{name}_int_s_r4_c_{i}",
                lambda i: f"{name}_int_s_r3_b_{i}",
                lambda i: f"{name}_int_s_r2_c_{i}",
                lambda i: f"{name}_int_s_r1_e_{i}",
                lambda i: f"{name}_w1_{i}",       # chunk 6 = r0
            ]
            print(f"; {name}: final c[k] = sum of overlapping chunks")
            for k in range(2 * n - 1):
                contributions = []
                for c in range(7):
                    i_in_chunk = k - c * N_SB
                    if 0 <= i_in_chunk < N_SB_RES:
                        contributions.append(
                            chunk_value[c](i_in_chunk))
                if not contributions:
                    expr = "(_ bv0 16)"
                else:
                    expr = addn(*contributions)
                print(f"(define-fun {name}_c{k} () (_ BitVec 16) "
                      f"{expr})")
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
    if cmp_qbits != qbits:
        print(f"; Comparison is modulo 2^{cmp_qbits}: extract low "
              f"{cmp_qbits} bits before comparing.")
        # Compare bvand A_res mask vs bvand B_res mask, where
        # mask = 2^cmp_qbits - 1.
        mask_val = (1 << cmp_qbits) - 1
        def cmp_lhs(i):
            return f"(bvand A_res{i} (_ bv{mask_val} {qbits}))"
        def cmp_rhs(i):
            return f"(bvand B_res{i} (_ bv{mask_val} {qbits}))"
    else:
        def cmp_lhs(i):
            return f"A_res{i}"
        def cmp_rhs(i):
            return f"B_res{i}"
    if single_coeff is not None:
        # Test only one specific coefficient — sanity check.
        print(f"; Restricted to coefficient {single_coeff} only.")
        diseq_expr = (f"(distinct {cmp_lhs(single_coeff)} "
                      f"{cmp_rhs(single_coeff)})")
    else:
        diseqs = []
        for i in range(n):
            diseqs.append(f"(distinct {cmp_lhs(i)} {cmp_rhs(i)})")
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
                   help="bitwidth of each coefficient (storage = 2^q)")
    p.add_argument("--cmp-qbits", type=int, default=None,
                   help="comparison bitwidth: compare results mod 2^this. "
                        "Defaults to --q. For Toom-Cook 4-way SABER, set "
                        "to 13 (SABER's actual modulus) while --q is 16 "
                        "(SABER's uint16_t storage).")
    p.add_argument("--algo-a", default="schoolbook",
                   choices=["schoolbook", "karatsuba", "karatsuba2",
                            "toom4"])
    p.add_argument("--algo-b", default="karatsuba",
                   choices=["schoolbook", "karatsuba", "karatsuba2",
                            "toom4"])
    p.add_argument("--single-coeff", type=int, default=None,
                   help="if set, assert disagreement on only this output coefficient")
    args = p.parse_args()
    emit_query(args.n, args.q, args.algo_a, args.algo_b,
               single_coeff=args.single_coeff,
               cmp_qbits=args.cmp_qbits)


if __name__ == "__main__":
    main()
