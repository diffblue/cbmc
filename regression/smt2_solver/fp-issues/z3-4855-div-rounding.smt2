; Z3#4855: fp.div with RTZ rounding on specific values
(set-logic QF_FP)
(declare-fun c () (_ FloatingPoint 8 24))
; 1.0 / 1.6 with RTZ
(define-fun b () (_ FloatingPoint 8 24) (fp.div RTZ
  (fp #b0 #b01111111 #b00000000000000000000000)
  (fp #b0 #b01111111 #b10011001100110011001101)))
; c / 2.0 >= 0 with RTZ
(assert (not (fp.lt (fp.div RTZ c
  (fp #b0 #b10000000 #b00000000000000000000000))
  (fp #b0 #b00000000 #b00000000000000000000000))))
(check-sat)
