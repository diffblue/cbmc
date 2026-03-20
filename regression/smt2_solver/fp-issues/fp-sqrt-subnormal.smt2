; fp.sqrt of subnormal input: sqrt(4 * 2^-149) = sqrt(2) * 2^-74
(set-logic QF_FP)
(declare-const r (_ FloatingPoint 8 24))
(assert (= r (fp.sqrt RNE (fp #b0 #b00000000 #b00000000000000000000100))))
(assert (not (= r (fp #b0 #b00110101 #b01101010000010011110011))))
(check-sat)
