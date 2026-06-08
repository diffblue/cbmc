(set-logic QF_BV)
; Variables-scaling: k=3 variables.
; Identity: sum over all k! permutations of x_1 * ... * x_k equals k! * product.
; Number of multiplications on LHS: k * k!
; Number of multiplications on RHS: k
(declare-fun x1 () (_ BitVec 16))
(declare-fun x2 () (_ BitVec 16))
(declare-fun x3 () (_ BitVec 16))
(define-fun lhs () (_ BitVec 16) (bvadd (bvadd (bvadd (bvadd (bvadd (bvmul (bvmul x1 x2) x3) (bvmul (bvmul x1 x3) x2)) (bvmul (bvmul x2 x1) x3)) (bvmul (bvmul x2 x3) x1)) (bvmul (bvmul x3 x1) x2)) (bvmul (bvmul x3 x2) x1)))
(define-fun rhs () (_ BitVec 16) (bvmul (_ bv6 16) (bvmul (bvmul x1 x2) x3)))
(assert (not (= lhs rhs)))
(check-sat)
(exit)
