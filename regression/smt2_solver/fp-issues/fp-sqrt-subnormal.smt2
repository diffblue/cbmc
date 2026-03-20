; fp.sqrt of a subnormal input:
; sqrt(4 * 2^-149) = 2^-73.5, which rounds (RNE) to 0x1AB504F3.
(set-logic QF_FP)
(declare-const r (_ FloatingPoint 8 24))
(assert (= r (fp.sqrt RNE (fp #b0 #b00000000 #b00000000000000000000100))))
(assert (not (= r (fp #b0 #b00110101 #b01101010000010011110011))))
(check-sat)
