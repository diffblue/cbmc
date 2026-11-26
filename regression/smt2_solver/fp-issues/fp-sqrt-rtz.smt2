; fp.sqrt(2.0) must honour the rounding mode:
;   RTZ and RNE yield 0x3FB504F3 (just below sqrt(2)),
;   RTP yields 0x3FB504F4 (just above sqrt(2)).
(set-logic QF_FP)
(assert (or
  (not (= (fp.sqrt RTZ (fp #b0 #b10000000 #b00000000000000000000000))
          (fp #b0 #b01111111 #b01101010000010011110011)))
  (not (= (fp.sqrt RNE (fp #b0 #b10000000 #b00000000000000000000000))
          (fp #b0 #b01111111 #b01101010000010011110011)))
  (not (= (fp.sqrt RTP (fp #b0 #b10000000 #b00000000000000000000000))
          (fp #b0 #b01111111 #b01101010000010011110100)))))
(check-sat)
