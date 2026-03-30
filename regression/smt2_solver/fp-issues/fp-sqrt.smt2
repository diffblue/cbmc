; Test fp.sqrt with various cases
(set-logic QF_FP)

; sqrt(4.0) = 2.0
(assert (fp.eq (fp.sqrt RNE
  (fp #b0 #b10000001 #b00000000000000000000000))
  (fp #b0 #b10000000 #b00000000000000000000000)))

; sqrt(9.0) = 3.0
(assert (fp.eq (fp.sqrt RNE
  (fp #b0 #b10000010 #b00100000000000000000000))
  (fp #b0 #b10000000 #b10000000000000000000000)))

; sqrt(NaN) = NaN
(assert (fp.isNaN (fp.sqrt RNE (_ NaN 8 24))))

; sqrt(-1) = NaN
(assert (fp.isNaN (fp.sqrt RNE (fp #b1 #b01111111 #b00000000000000000000000))))

; sqrt(+0) = +0
(assert (fp.isZero (fp.sqrt RNE (fp #b0 #b00000000 #b00000000000000000000000))))

; sqrt(+inf) = +inf
(assert (fp.isInfinite (fp.sqrt RNE (_ +oo 8 24))))

(check-sat)
