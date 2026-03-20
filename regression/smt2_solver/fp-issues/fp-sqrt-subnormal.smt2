; fp.sqrt of subnormal input gives incorrect result
; sqrt(4 * 2^-149) should be 2 * 2^(-149/2) ≈ 7.487e-23
; The correct Float32 result is 0x1AB504F3
(set-logic QF_FP)
(declare-const r (_ FloatingPoint 8 24))
(assert (= r (fp.sqrt RNE (fp #b0 #b00000000 #b00000000000000000000100))))
(assert (not (= r (fp #b0 #b00110101 #b01011010000010011110011))))
(check-sat)
