; Z3#2596: fp.eq(NaN, NaN) is always false
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.isNaN x))
(assert (fp.eq x x))
(check-sat)
