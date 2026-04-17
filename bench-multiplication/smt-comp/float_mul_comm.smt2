; IEEE 754 binary32 (float) multiplication commutativity
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(assert (not (fp.eq (fp.mul RNE a b) (fp.mul RNE b a))))
(check-sat)
(exit)
