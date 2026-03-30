; fp.fma is now supported. Tests basic fp.fma satisfiability.
; Based on Z3#7162 and CVC5#11139.

(set-logic QF_FP)
(declare-const a (_ FloatingPoint 11 53))
(declare-const b (_ FloatingPoint 11 53))
(declare-const c (_ FloatingPoint 11 53))
(assert (= (fp.fma RNE a b c)
  (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000)))
(check-sat)
