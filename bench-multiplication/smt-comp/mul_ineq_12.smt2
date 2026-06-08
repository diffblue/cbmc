; If a <= b and c > 0 and no overflow, then a*c <= b*c
(set-logic QF_BV)
(declare-fun a () (_ BitVec 12))
(declare-fun b () (_ BitVec 12))
(declare-fun c () (_ BitVec 12))
(assert (bvule a b))
(assert (not (= c (_ bv0 12))))
; Assume no overflow for both products
(define-fun wa () (_ BitVec 24) ((_ zero_extend 12) a))
(define-fun wb () (_ BitVec 24) ((_ zero_extend 12) b))
(define-fun wc () (_ BitVec 24) ((_ zero_extend 12) c))
(assert (= ((_ extract 23 12) (bvmul wa wc)) (_ bv0 12)))
(assert (= ((_ extract 23 12) (bvmul wb wc)) (_ bv0 12)))
; Check monotonicity
(assert (not (bvule (bvmul a c) (bvmul b c))))
(check-sat)
(exit)
