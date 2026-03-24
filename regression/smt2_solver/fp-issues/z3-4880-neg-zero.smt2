; Z3#4880: -0 is negative per fp.isNegative (should be unsat)
(set-logic QF_FP)
(assert (not (fp.isNegative (fp #b1 #b00000000 #b00000000000000000000000))))
(check-sat)
