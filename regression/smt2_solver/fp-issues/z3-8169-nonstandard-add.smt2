; Z3#8169: fp.add on non-standard sort (_ FloatingPoint 2 24)
; adding +0 to x gives x, so x > x is always false
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 2 24))
(assert (fp.gt (fp.add RNE x (fp #b0 #b00 #b00000000000000000000000)) x))
(check-sat)
