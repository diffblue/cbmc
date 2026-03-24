; Z3#8185: fp.to_real unsupported
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (= (fp.to_real x) 0.5))
(check-sat)
