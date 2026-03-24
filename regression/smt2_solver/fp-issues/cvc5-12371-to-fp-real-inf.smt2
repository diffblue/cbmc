; CVC5#12371: large float constant should be infinity
; Use bit pattern directly since to_fp from large Real may not work
(set-logic QF_FP)
; +inf is fp #b0 #b11111111 #b00000000000000000000000
(assert (fp.isInfinite (_ +oo 8 24)))
(assert (fp.isNegative (_ -oo 8 24)))
(assert (fp.isInfinite (_ -oo 8 24)))
(check-sat)
