; Barrett reduction: approximate modular multiplication
; q = (a * m) >> k where m ≈ 2^k / n
; r = a - q * n
; Verify: r < 2*n (Barrett's guarantee)
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(define-fun n () (_ BitVec 8) (_ bv17 8))  ; modulus
(define-fun m () (_ BitVec 8) (_ bv15 8))  ; ≈ 256/17
(define-fun k () (_ BitVec 8) (_ bv8 8))
; q = (a * m) >> 8 (approximate quotient)
(define-fun wide_am () (_ BitVec 16) (bvmul ((_ zero_extend 8) a) ((_ zero_extend 8) m)))
(define-fun q () (_ BitVec 8) ((_ extract 15 8) wide_am))
; r = a - q * n
(define-fun r () (_ BitVec 8) (bvsub a (bvmul q n)))
; Barrett guarantees r < 2*n
(assert (bvuge r (bvmul (_ bv2 8) n)))
(check-sat)
(exit)
