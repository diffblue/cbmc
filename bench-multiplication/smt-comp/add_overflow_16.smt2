; Unsigned addition overflow detection equivalence
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(define-fun wa () (_ BitVec 17) ((_ zero_extend 1) a))
(define-fun wb () (_ BitVec 17) ((_ zero_extend 1) b))
(define-fun wide_sum () (_ BitVec 17) (bvadd wa wb))
(define-fun overflow () Bool (= ((_ extract 16 16) wide_sum) #b1))
(define-fun narrow_sum () (_ BitVec 16) (bvadd a b))
; If no overflow, narrow == low bits of wide
(assert overflow)
(assert (not (= narrow_sum ((_ extract 15 0) wide_sum))))
(check-sat)
(exit)
