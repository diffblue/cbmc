; Test to_fp from bitvector (reinterpret cast).
; 0x3F800000 reinterpreted as Float32 should be 1.0.

(set-logic QF_FP)
(assert (not (fp.eq ((_ to_fp 8 24) (_ bv1065353216 32))
                    (fp #b0 #b01111111 #b00000000000000000000000))))
(check-sat)
