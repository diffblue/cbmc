; Regression: fp.isZero(-0) should be true
(set-logic QF_FP)
(assert (not (fp.isZero (fp #b1 #b00000000 #b00000000000000000000000))))
(check-sat)
