; Z3#4880: fp.min(-0, +0) is negative (quantifier-free core)
(set-logic QF_FP)
(assert (not (fp.isNegative (fp.min
  (fp #b1 #b00000000 #b00000000000000000000000)
  (fp #b0 #b00000000 #b00000000000000000000000)))))
(check-sat)
