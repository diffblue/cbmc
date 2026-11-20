; roundToIntegral RTZ 3.5f should be 3.0f (Float32).
; 3.5 = fp #b0 #b10000000 #b11000000000000000000000
; 3.0 = fp #b0 #b10000000 #b10000000000000000000000

(set-logic QF_FP)
(assert (not (= (fp.roundToIntegral RTZ
  (fp #b0 #b10000000 #b11000000000000000000000))
  (fp #b0 #b10000000 #b10000000000000000000000))))
(check-sat)
