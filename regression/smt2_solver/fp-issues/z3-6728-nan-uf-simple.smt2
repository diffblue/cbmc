; Z3#6728: NaN structural equality through UF
(set-logic QF_FPUF)
(declare-fun f ((_ FloatingPoint 8 24)) Bool)
(assert (f (_ NaN 8 24)))
(assert (not (f (_ NaN 8 24))))
(check-sat)
