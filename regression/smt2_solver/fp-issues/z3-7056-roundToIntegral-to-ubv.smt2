; Z3#7056: roundToIntegral RTZ with to_fp_unsigned and fp.to_ubv
(set-logic QF_FP)
(declare-fun x () (_ BitVec 16))
(define-fun fval () (_ FloatingPoint 8 8) ((_ to_fp 8 8) x))
(define-fun rounded () (_ FloatingPoint 8 8) (fp.roundToIntegral RTZ fval))
(define-fun as_ubv () (_ BitVec 128) ((_ fp.to_ubv 128) RTZ rounded))
(define-fun back () (_ FloatingPoint 8 8) ((_ to_fp_unsigned 8 8) RTZ as_ubv))
; For positive non-zero finite values, roundtrip should preserve
(assert (fp.isPositive rounded))
(assert (not (fp.isZero rounded)))
(assert (not (fp.isNaN rounded)))
(assert (not (fp.isInfinite rounded)))
(assert (not (fp.eq back rounded)))
(check-sat)
