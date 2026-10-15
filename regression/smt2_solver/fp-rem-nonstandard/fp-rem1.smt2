; Based on Z3#2381: fp.rem producing incorrect result.
; fp.rem(3.0, 2.0) should be -1.0 per IEEE 754 remainder:
;   round(3.0/2.0) = round(1.5) = 2 (ties to even), so rem = 3 - 2*2 = -1
; This formula asserts rem(3.0, 2.0) != -1.0, which should be UNSAT.

(set-logic QF_FP)

; 3.0 as Float32: sign=0, exp=10000000, mant=10000000000000000000000
(define-fun three () (_ FloatingPoint 8 24)
  (fp #b0 #b10000000 #b10000000000000000000000))

; 2.0 as Float32: sign=0, exp=10000000, mant=00000000000000000000000
(define-fun two () (_ FloatingPoint 8 24)
  (fp #b0 #b10000000 #b00000000000000000000000))

; -1.0 as Float32: sign=1, exp=01111111, mant=00000000000000000000000
(define-fun neg_one () (_ FloatingPoint 8 24)
  (fp #b1 #b01111111 #b00000000000000000000000))

(assert (not (= (fp.rem three two) neg_one)))
(check-sat)
