; Converting the integer 1 from source widths of the form 2^k+1 must
; give 1.0 (#x3f800000), as for any other width.
(set-logic QF_BVFP)
(declare-const r3 (_ BitVec 32))
(declare-const r5 (_ BitVec 32))
(declare-const r9 (_ BitVec 32))
(declare-const s3 (_ BitVec 32))
(assert (= ((_ to_fp 8 24) r3) ((_ to_fp_unsigned 8 24) RNE #b001)))
(assert (= ((_ to_fp 8 24) r5) ((_ to_fp_unsigned 8 24) RNE #b00001)))
(assert (= ((_ to_fp 8 24) r9) ((_ to_fp_unsigned 8 24) RNE #b000000001)))
(assert (= ((_ to_fp 8 24) s3) ((_ to_fp 8 24) RNE #b001)))
(check-sat)
(get-value (r3 r5 r9 s3))
