;
; Wrong-width operand for the bit-pattern reinterpretation overload of
; `to_fp`: the operand must be 1+eb+(sb-1) = 64 bits for a double, so
; the 8-bit bit-vector below should be rejected at parse time.
;
(define-fun B0 () Bool (=
  ((_ to_fp 11 53) (_ bv1 8))
  (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000)))

(assert (not B0))

(check-sat)

(exit)
