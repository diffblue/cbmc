(set-logic QF_BV)
; Binomial identity of degree 2 at bitwidth 8:
; (a+b)^2 = sum_{i=0}^{2} C(2,i) a^i b^{2-i}
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(define-fun lhs () (_ BitVec 8) (bvmul (bvadd a b) (bvadd a b)))
(define-fun rhs () (_ BitVec 8) (bvadd (bvadd (bvmul b b) (bvmul (_ bv2 8) (bvmul a b))) (bvmul a a)))
(assert (not (= lhs rhs)))
(check-sat)
(exit)
