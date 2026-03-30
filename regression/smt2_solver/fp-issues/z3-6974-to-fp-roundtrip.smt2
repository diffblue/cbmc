; Z3#6974: to_fp from signed BV and back should be identity for small values.
; Converting a signed 8-bit integer to Float32 with RTZ and back should
; preserve the value (all 8-bit integers are exactly representable in Float32).
(set-logic QF_FP)
(declare-fun s1 () (_ BitVec 8))
(define-fun s2 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTZ s1))
(define-fun s3 () (_ BitVec 8) ((_ fp.to_sbv 8) RTZ s2))
(assert (not (= s1 s3)))
(check-sat)
