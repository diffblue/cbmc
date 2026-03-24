; Based on Bitwuzla#130: fp.div on non-standard FP format (_ FloatingPoint 4 12).
; Bitwuzla incorrectly returned unsat due to a SymFPU bug in fp.div
; for non-standard formats.

(set-logic QF_FP)
(declare-const a (_ FloatingPoint 4 12))
(declare-const b (_ FloatingPoint 4 12))

; fp.div RNA a b should be satisfiable for non-NaN, non-zero b
(assert (not (fp.isNaN a)))
(assert (not (fp.isNaN b)))
(assert (not (fp.isZero b)))
(assert (not (fp.isInfinite b)))
(assert (fp.gt (fp.div RNA a b) (fp #b0 #b0000 #b00000000000)))
(check-sat)
