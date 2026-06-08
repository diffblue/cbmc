(set-logic QF_BV)
; Binomial identity of degree 2 at bitwidth 16:
; (a+b)^2 = sum_{i=0}^{2} C(2,i) a^i b^{2-i}
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(define-fun lhs () (_ BitVec 16) (bvmul (bvadd a b) (bvadd a b)))
(define-fun rhs () (_ BitVec 16) (bvadd (bvadd (bvmul b b) (bvmul (_ bv2 16) (bvmul a b))) (bvmul a a)))
(assert (not (= lhs rhs)))
(check-sat)
(exit)
