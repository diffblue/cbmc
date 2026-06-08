#!/usr/bin/env python3
"""
Variables-scaling benchmark generator for Paper 2.

Generates polynomial-identity benchmarks where the number of variables
k varies from 2 to 8. The identity at k variables is:

  sum_{sigma in permutations of x_1..x_k} (x_sigma(1) * x_sigma(2) * ... * x_sigma(k))
  ==
  k! * (x_1 * x_2 * ... * x_k)

This tests the Groebner basis solver on multiplication-commutativity
identities with increasing numbers of variables. At k=2, this is
simple commutativity a*b = b*a (trivial). At k=3, it's
(abc+acb+bac+bca+cab+cba) = 6*abc (six terms, but all equal by
commutativity of associative multiplication). In general, the sum
is k! * product, and the identity holds.

For k=5,6,7,8 the formula has k! terms, which stress-tests the
Groebner basis's ability to identify variable commutativity at scale.
"""

import os
import itertools

BW = 16

def make_commutativity_k(k):
    """Generate a k-variable commutativity identity."""
    varnames = [f"x{i}" for i in range(1, k + 1)]
    decls = "\n".join(f"(declare-fun {v} () (_ BitVec {BW}))" for v in varnames)
    
    # Canonical product x_1 * x_2 * ... * x_k
    def prod(vars):
        if len(vars) == 1:
            return vars[0]
        return f"(bvmul {prod(vars[:-1])} {vars[-1]})"
    
    canonical = prod(varnames)
    
    # Sum of all k! permutations
    perms = list(itertools.permutations(varnames))
    perm_prods = [prod(list(p)) for p in perms]
    
    def sum_of(terms):
        if len(terms) == 1:
            return terms[0]
        return f"(bvadd {sum_of(terms[:-1])} {terms[-1]})"
    
    sum_expr = sum_of(perm_prods)
    
    # Multiplier: k! as a BV constant
    import math
    factorial_k = math.factorial(k)
    rhs = f"(bvmul (_ bv{factorial_k} {BW}) {canonical})"
    
    smt = f"""(set-logic QF_BV)
; Variables-scaling: k={k} variables.
; Identity: sum over all k! permutations of x_1 * ... * x_k equals k! * product.
; Number of multiplications on LHS: k * k!
; Number of multiplications on RHS: k
{decls}
(define-fun lhs () (_ BitVec {BW}) {sum_expr})
(define-fun rhs () (_ BitVec {BW}) {rhs})
(assert (not (= lhs rhs)))
(check-sat)
(exit)
"""
    return smt

def main():
    outdir = os.path.dirname(os.path.abspath(__file__))
    for k in [2, 3, 4, 5, 6]:
        smt = make_commutativity_k(k)
        fname = os.path.join(outdir, f"varscale_k{k}_bw{BW}.smt2")
        with open(fname, "w") as f:
            f.write(smt)
        print(f"wrote {fname} ({len(smt.splitlines())} lines)")

if __name__ == "__main__":
    main()
