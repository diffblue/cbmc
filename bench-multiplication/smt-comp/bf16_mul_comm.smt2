; bfloat16 multiplication commutativity
; bf16: 8-bit exponent, 8-bit significand (7-bit mantissa + 1 implicit)
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 8 8))
(declare-fun b () (_ FloatingPoint 8 8))
(assert (not (fp.eq (fp.mul RNE a b) (fp.mul RNE b a))))
(check-sat)
(exit)
