; Fixed-point multiplication: (a * b) >> 8 where a,b are 8.8 fixed-point
; Verify: result is within 1 ULP of the true value
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
; Full 32-bit product
(define-fun wa () (_ BitVec 32) ((_ zero_extend 16) a))
(define-fun wb () (_ BitVec 32) ((_ zero_extend 16) b))
(define-fun full_prod () (_ BitVec 32) (bvmul wa wb))
; Fixed-point result: shift right by 8 (the fractional bits)
(define-fun fp_result () (_ BitVec 16) ((_ extract 23 8) full_prod))
; Truncated result (what naive code computes)
(define-fun trunc_result () (_ BitVec 16) ((_ extract 23 8) ((_ zero_extend 16) (bvmul a b))))
; These should be equal (no information loss in the relevant bits)
(assert (not (= fp_result trunc_result)))
(check-sat)
(exit)
