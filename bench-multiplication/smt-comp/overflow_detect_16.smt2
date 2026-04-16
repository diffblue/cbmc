; Verify unsigned multiplication overflow detection
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
; Wide multiplication
(define-fun wa () (_ BitVec 32) ((_ zero_extend 16) a))
(define-fun wb () (_ BitVec 32) ((_ zero_extend 16) b))
(define-fun wide_prod () (_ BitVec 32) (bvmul wa wb))
; Overflow iff high 16 bits are nonzero
(define-fun overflow () Bool (not (= ((_ extract 31 16) wide_prod) (_ bv0 16))))
; Narrow product
(define-fun narrow_prod () (_ BitVec 16) (bvmul a b))
; If no overflow, narrow == low bits of wide
(assert overflow)
(assert (not (= narrow_prod ((_ extract 15 0) wide_prod))))
(check-sat)
(exit)
