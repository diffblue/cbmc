; Z3#8345: fp.to_real unsupported
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 11 53))
(assert (= (fp.to_real x) 1.0))
(check-sat)
