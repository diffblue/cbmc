; Test to_fp conversion between FP sorts (double to float).
; Converting 1.0 (Float64) to Float32 should give 1.0 (Float32).

(set-logic QF_FP)
; 1.0 as Float64
(define-fun one_d () (_ FloatingPoint 11 53)
  (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000))
; 1.0 as Float32
(define-fun one_f () (_ FloatingPoint 8 24)
  (fp #b0 #b01111111 #b00000000000000000000000))

(assert (not (= ((_ to_fp 8 24) RNE one_d) one_f)))
(check-sat)
