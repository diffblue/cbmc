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
                   choices=["schoolbook", "karatsuba"])
    p.add_argument("--algo-b", default="karatsuba",
                   choices=["schoolbook", "karatsuba"])
    p.add_argument("--single-coeff", type=int, default=None,
                   help="if set, assert disagreement on only this output coefficient")
    args = p.parse_args()
    emit_query(args.n, args.q, args.algo_a, args.algo_b,
               single_coeff=args.single_coeff)


if __name__ == "__main__":
    main()
