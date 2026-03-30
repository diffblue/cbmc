; Z3#6674: fp.fma on non-standard sort (_ FloatingPoint 3 2).
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 3 2))
(assert (= (fp #b0 #b000 #b0) (fp.fma RNE x x (fp #b0 #b000 #b0))))
(check-sat)
