; Regression: fp.isSubnormal(-0) should be false (-0 is zero, not subnormal)
(set-logic QF_FP)
(assert (fp.isSubnormal (fp #b1 #b00000000 #b00000000000000000000000)))
(check-sat)
