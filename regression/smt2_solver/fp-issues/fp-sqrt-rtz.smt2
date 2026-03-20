; fp.sqrt(2.0) with RTZ should be 0x3FB504F2 (rounded down)
; Currently returns 0x3FB504F3 (same as RNE) — rounding mode ignored
(set-logic QF_FP)
(assert (not (= (fp.sqrt RTZ (fp #b0 #b10000000 #b00000000000000000000000))
               (fp #b0 #b01111111 #b01101010000010011110010))))
(check-sat)
