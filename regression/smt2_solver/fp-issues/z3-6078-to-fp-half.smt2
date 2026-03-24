; Z3#6078: to_fp from constant Real 0.5 should give 0.5
(set-logic QF_FP)
(assert (not (fp.eq
  ((_ to_fp 11 53) RNE 0.5)
  (fp #b0 #b01111111110 #b0000000000000000000000000000000000000000000000000000))))
(check-sat)
