; Test fp.isSubnormal, fp.isNegative, fp.isPositive predicates.

(set-logic QF_FP)

; A subnormal Float32 exists
(declare-const s (_ FloatingPoint 8 24))
(assert (fp.isSubnormal s))

; A negative normal value exists
(declare-const n (_ FloatingPoint 8 24))
(assert (fp.isNegative n))
(assert (fp.isNormal n))

; A positive value exists
(declare-const p (_ FloatingPoint 8 24))
(assert (fp.isPositive p))

; NaN is neither negative nor positive
(assert (not (fp.isNegative (_ NaN 8 24))))
(assert (not (fp.isPositive (_ NaN 8 24))))

(check-sat)
