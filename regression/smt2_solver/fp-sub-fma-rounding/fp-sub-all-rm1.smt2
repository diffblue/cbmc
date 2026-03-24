; Based on Z3#7162: Test all rounding modes with fp.sub on Float64.
; IEEE 754: x - x == +0 for all rounding modes except RTN, where it is -0.

(set-logic QF_FP)
(declare-const a1 (_ FloatingPoint 11 53))
(declare-const a2 (_ FloatingPoint 11 53))
(declare-const a3 (_ FloatingPoint 11 53))
(declare-const a4 (_ FloatingPoint 11 53))
(declare-const a5 (_ FloatingPoint 11 53))

(define-fun pzero () (_ FloatingPoint 11 53)
  (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000))
(define-fun nzero () (_ FloatingPoint 11 53)
  (fp #b1 #b00000000000 #b0000000000000000000000000000000000000000000000000000))

; x - x == +0 for RNE, RNA, RTP, RTZ (when x is finite)
(assert (not (fp.isNaN a1)))
(assert (not (fp.isInfinite a1)))
(assert (= (fp.sub RNE a1 a1) pzero))

(assert (not (fp.isNaN a2)))
(assert (not (fp.isInfinite a2)))
(assert (= (fp.sub RNA a2 a2) pzero))

(assert (not (fp.isNaN a3)))
(assert (not (fp.isInfinite a3)))
(assert (= (fp.sub RTP a3 a3) pzero))

; x - x == -0 for RTN (round toward negative)
(assert (not (fp.isNaN a4)))
(assert (not (fp.isInfinite a4)))
(assert (= (fp.sub RTN a4 a4) nzero))

(assert (not (fp.isNaN a5)))
(assert (not (fp.isInfinite a5)))
(assert (= (fp.sub RTZ a5 a5) pzero))

(check-sat)
