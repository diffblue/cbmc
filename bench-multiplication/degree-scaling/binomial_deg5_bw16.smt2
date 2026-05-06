(set-logic QF_BV)
; Binomial identity of degree 5 at bitwidth 16:
; (a+b)^5 = sum_{i=0}^{5} C(5,i) a^i b^{5-i}
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(define-fun lhs () (_ BitVec 16) (bvmul (bvmul (bvmul (bvmul (bvadd a b) (bvadd a b)) (bvadd a b)) (bvadd a b)) (bvadd a b)))
(define-fun rhs () (_ BitVec 16) (bvadd (bvadd (bvadd (bvadd (bvadd (bvmul (bvmul (bvmul (bvmul b b) b) b) b) (bvmul (_ bv5 16) (bvmul a (bvmul (bvmul (bvmul b b) b) b)))) (bvmul (_ bv10 16) (bvmul (bvmul a a) (bvmul (bvmul b b) b)))) (bvmul (_ bv10 16) (bvmul (bvmul (bvmul a a) a) (bvmul b b)))) (bvmul (_ bv5 16) (bvmul (bvmul (bvmul (bvmul a a) a) a) b))) (bvmul (bvmul (bvmul (bvmul a a) a) a) a)))
(assert (not (= lhs rhs)))
(check-sat)
(exit)
