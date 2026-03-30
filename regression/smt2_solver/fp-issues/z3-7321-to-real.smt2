; Z3#7321: fp.to_real unsupported
(set-logic QF_FP)
(declare-fun s0 () (_ FloatingPoint 4 4))
(assert (= (fp.to_real s0) 1.0))
(check-sat)
