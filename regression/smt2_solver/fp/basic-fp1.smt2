(set-logic FP)

(define-fun Areal () (_ FloatingPoint 11 53) ((_ to_fp 11 53) roundNearestTiesToEven 1.185043))
(define-fun Ahexa () (_ FloatingPoint 11 53) (fp #b0 #b01111111111 #x2f5efa615a8df))

; should be the same
(assert (not (= Areal Ahexa)))

(check-sat)
