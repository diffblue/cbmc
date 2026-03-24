; Based on CVC5#11139: fp.div with different rounding modes on Float64.
; CVC5 crashes with symfpu postcondition failure on fp.div RTN.
; Test that CBMC's solver handles fp.div correctly.

(set-logic QF_FP)
(declare-const a (_ FloatingPoint 11 53))
(declare-const b (_ FloatingPoint 11 53))

(define-fun pzero () (_ FloatingPoint 11 53)
  (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000))

; (a * a) / b == +0.0 should be satisfiable (e.g., a == 0, b == 1)
(assert (= (fp.div RTN (fp.mul RTP a a) b) pzero))
(assert (not (fp.isZero b)))
(assert (not (fp.isNaN b)))
(assert (not (fp.isInfinite b)))
(check-sat)
