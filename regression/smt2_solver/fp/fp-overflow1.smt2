; Based on Z3#4673: Overflow should produce infinity.
; x > 0, (x * 2) * 0.5 > x should be satisfiable.
; When x = FLT_MAX, x*2 overflows to +inf, then +inf * 0.5 = +inf > FLT_MAX.

(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.gt x (fp #b0 #b00000000 #b00000000000000000000000)))
(assert (fp.gt
  (fp.mul RNE (fp.mul RNE x (fp #b0 #b10000000 #b00000000000000000000000))
              (fp #b0 #b01111110 #b00000000000000000000000))
  x))
(check-sat)
