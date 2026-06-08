(set-logic QF_BV)
; Binomial identity of degree 4 at bitwidth 8:
; (a+b)^4 = sum_{i=0}^{4} C(4,i) a^i b^{4-i}
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(define-fun lhs () (_ BitVec 8) (bvmul (bvmul (bvmul (bvadd a b) (bvadd a b)) (bvadd a b)) (bvadd a b)))
(define-fun rhs () (_ BitVec 8) (bvadd (bvadd (bvadd (bvadd (bvmul (bvmul (bvmul b b) b) b) (bvmul (_ bv4 8) (bvmul a (bvmul (bvmul b b) b)))) (bvmul (_ bv6 8) (bvmul (bvmul a a) (bvmul b b)))) (bvmul (_ bv4 8) (bvmul (bvmul (bvmul a a) a) b))) (bvmul (bvmul (bvmul a a) a) a)))
(assert (not (= lhs rhs)))
(check-sat)
(exit)
