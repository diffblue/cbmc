;
; convert (_ bv1 1) to double precision FP,
; and check whether that is equal to 1.0.
;
(define-fun B0 () Bool (=
  ((_ to_fp_unsigned 11 53) roundNearestTiesToAway (_ bv1 1))
  (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000)))

(assert (not B0))

; expected to be UNSAT, i.e., they are equal
(check-sat)

(exit)
