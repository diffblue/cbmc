; Z3#4858: fp.sub and fp.add with RTZ rounding
(set-logic QF_FP)
(declare-fun f () (_ FloatingPoint 8 24))
(declare-fun h () (_ FloatingPoint 8 24))
; f - (f + h) with RTZ: if h is subnormal and f is large, result is -h or 0
(assert (not (fp.isNaN f)))
(assert (not (fp.isInfinite f)))
(assert (fp.isSubnormal h))
(assert (fp.isNormal f))
(assert (not (fp.eq (fp.sub RTZ f (fp.add RTZ f h)) (fp.neg h))))
(check-sat)
