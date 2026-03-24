; Z3#7162: fp.sub RNA with fp.fma RTN on Float64.
(set-logic QF_FP)
(declare-const a0 (_ FloatingPoint 11 53))
(declare-const a1 (_ FloatingPoint 11 53))
(declare-const a3 (_ FloatingPoint 11 53))
(declare-const a4 (_ FloatingPoint 11 53))
(assert (= (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)
  (fp.sub RNA a4 (fp.fma RTN a3 a1 a0))))
(check-sat)
