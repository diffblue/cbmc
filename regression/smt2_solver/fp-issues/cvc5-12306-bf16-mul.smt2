; CVC5#12306: BF16 multiplication with bound checking
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 8))
(declare-const c (_ FloatingPoint 8 8))
(assert (not (fp.isNaN x)))
(assert (not (fp.isNaN c)))
(assert (fp.gt (fp.mul RNE (fp.mul RNE c x) x) (fp #b0 #b10000010 #b0000000)))
(check-sat)
