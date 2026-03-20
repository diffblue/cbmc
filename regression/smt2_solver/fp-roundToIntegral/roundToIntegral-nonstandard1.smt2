; Based on Z3#4841: roundToIntegral on non-standard FP sort.
; roundToIntegral RTZ 3.96875 should be 3.0 in (_ FloatingPoint 2 6).
; 3.96875 = fp #b0 #b10 #b11111
; 3.0     = fp #b0 #b10 #b10000
; This formula asserts the result is NOT 3.0, so it should be UNSAT.

(set-logic QF_FP)
(assert (not (= (fp.roundToIntegral RTZ (fp #b0 #b10 #b11111))
               (fp #b0 #b10 #b10000))))
(check-sat)
