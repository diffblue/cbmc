;
; Reinterpret the 64-bit IEEE-754 interchange pattern of 1.0
; (0x3FF0000000000000 = 4607182418800017408) as a double via the
; single-argument bit-pattern overload of to_fp, and check it equals 1.0.
;
(define-fun B0 () Bool (=
  ((_ to_fp 11 53) (_ bv4607182418800017408 64))
  (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000)))

(assert (not B0))

; expected to be UNSAT, i.e., they are equal
(check-sat)

(exit)
