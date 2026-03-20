; fp.sqrt(2.0) with RTZ should be 0x3FB504F3 (floor of sqrt(2))
; sqrt(2) ≈ 1.41421356..., F3 = 1.41421353... < sqrt(2) < F4 = 1.41421365...
(set-logic QF_FP)
(assert (not (= (fp.sqrt RTZ (fp #b0 #b10000000 #b00000000000000000000000))
               (fp #b0 #b01111111 #b01101010000010011110011))))
(check-sat)
