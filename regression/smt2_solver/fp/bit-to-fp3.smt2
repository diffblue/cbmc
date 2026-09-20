;
; Reinterpret the 32-bit IEEE-754 interchange pattern of 1.0f
; (0x3F800000 = 1065353216) as a single via the single-argument
; bit-pattern overload of to_fp.  Confirms the width plumbing isn't
; hard-wired to double.
;
(define-fun B0 () Bool (=
  ((_ to_fp 8 24) (_ bv1065353216 32))
  (fp #b0 #b01111111 #b00000000000000000000000)))

(assert (not B0))

; expected to be UNSAT, i.e., they are equal
(check-sat)

(exit)
