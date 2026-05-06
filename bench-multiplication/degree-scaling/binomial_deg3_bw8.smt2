(set-logic QF_BV)
; Binomial identity of degree 3 at bitwidth 8:
; (a+b)^3 = sum_{i=0}^{3} C(3,i) a^i b^{3-i}
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(define-fun lhs () (_ BitVec 8) (bvmul (bvmul (bvadd a b) (bvadd a b)) (bvadd a b)))
(define-fun rhs () (_ BitVec 8) (bvadd (bvadd (bvadd (bvmul (bvmul b b) b) (bvmul (_ bv3 8) (bvmul a (bvmul b b)))) (bvmul (_ bv3 8) (bvmul (bvmul a a) b))) (bvmul (bvmul a a) a)))
(assert (not (= lhs rhs)))
(check-sat)
(exit)
