; Z3#5572: multiplication and roundToIntegral
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.gt x (fp #b0 #b00000000 #b00000000000000000000000)))
(assert (fp.lt x (fp #b0 #b10000110 #b00000000000000000000000)))
; x * pi truncated to integer equals 10.0
(assert (fp.eq (fp.roundToIntegral RTZ (fp.mul RNE x
  (fp #b0 #b10000000 #b10010010000111111011011)))
  (fp #b0 #b10000010 #b01000000000000000000000)))
(check-sat)
