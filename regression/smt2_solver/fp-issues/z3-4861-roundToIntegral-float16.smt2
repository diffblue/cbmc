; Z3#4861: roundToIntegral RNE on Float16
; a = 2.0078125 (fp #b0 #b10000 #b0000001000), roundToIntegral RNE = 2.0
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 5 11))
(declare-fun b () (_ FloatingPoint 5 11))
(assert (= b (fp.roundToIntegral RNE a)))
(assert (= b (fp #b0 #b10000 #b0000000000)))
(check-sat)
