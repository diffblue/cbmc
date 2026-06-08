; Rust checked_mul: returns None on overflow
; Verify: if checked_mul returns Some(r), then r == a*b (no overflow)
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
; Wide multiplication to detect overflow
(define-fun wa () (_ BitVec 32) ((_ zero_extend 16) a))
(define-fun wb () (_ BitVec 32) ((_ zero_extend 16) b))
(define-fun wide_prod () (_ BitVec 32) (bvmul wa wb))
(define-fun has_overflow () Bool (not (= ((_ extract 31 16) wide_prod) (_ bv0 16))))
; Narrow product
(define-fun narrow_prod () (_ BitVec 16) (bvmul a b))
; If no overflow, narrow product equals low bits of wide product
(assert (not has_overflow))
(assert (not (= narrow_prod ((_ extract 15 0) wide_prod))))
(check-sat)
(exit)
