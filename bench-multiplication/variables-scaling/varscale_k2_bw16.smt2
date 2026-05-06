(set-logic QF_BV)
; Variables-scaling: k=2 variables.
; Identity: sum over all k! permutations of x_1 * ... * x_k equals k! * product.
; Number of multiplications on LHS: k * k!
; Number of multiplications on RHS: k
(declare-fun x1 () (_ BitVec 16))
(declare-fun x2 () (_ BitVec 16))
(define-fun lhs () (_ BitVec 16) (bvadd (bvmul x1 x2) (bvmul x2 x1)))
(define-fun rhs () (_ BitVec 16) (bvmul (_ bv2 16) (bvmul x1 x2)))
(assert (not (= lhs rhs)))
(check-sat)
(exit)
