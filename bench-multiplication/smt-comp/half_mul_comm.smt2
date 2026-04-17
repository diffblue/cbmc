; IEEE 754 binary16 (half-float) multiplication commutativity
; half: 5-bit exponent, 11-bit significand
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 5 11))
(declare-fun b () (_ FloatingPoint 5 11))
(assert (not (fp.eq (fp.mul RNE a b) (fp.mul RNE b a))))
(check-sat)
(exit)
