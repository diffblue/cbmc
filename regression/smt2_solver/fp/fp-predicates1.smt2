; Test fp.isSubnormal, fp.isNegative, fp.isPositive predicates.

(set-logic QF_FP)

; A subnormal Float32 exists, and at least one concrete subnormal
; bit-pattern is classified as subnormal (and not zero / not normal).
(declare-const s (_ FloatingPoint 8 24))
(assert (fp.isSubnormal s))
(assert (not (fp.isZero s)))

; Smallest positive Float32 subnormal: exponent = 0, mantissa = 0...01
(assert (fp.isSubnormal
          (fp #b0 #b00000000 #b00000000000000000000001)))
(assert (not (fp.isNormal
          (fp #b0 #b00000000 #b00000000000000000000001))))

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

; Negative zero is negative, positive zero is positive
(assert (fp.isNegative (fp #b1 #b00000000 #b00000000000000000000000)))
(assert (not (fp.isNegative (fp #b0 #b00000000 #b00000000000000000000000))))
(assert (fp.isPositive (fp #b0 #b00000000 #b00000000000000000000000)))
(assert (not (fp.isPositive (fp #b1 #b00000000 #b00000000000000000000000))))

(check-sat)

; Negative coverage: each of these would be `sat` if the corresponding
; predicate over-approximated. Expect `unsat` instead.
(check-sat-assuming
  ((fp.isPositive (fp #b1 #b00000000 #b00000000000000000000000)))) ; -0
(check-sat-assuming
  ((fp.isNegative (fp #b0 #b00000000 #b00000000000000000000000)))) ; +0
(check-sat-assuming
  ((fp.isSubnormal (fp #b0 #b01111111 #b00000000000000000000000)))) ; 1.0
