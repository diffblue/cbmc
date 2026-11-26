; Z3#6972: to_fp from BV and fp.isNaN
(set-logic QF_FP)
(declare-fun bv () (_ BitVec 32))
; to_fp(0x7FC00000) should be NaN (quiet NaN)
(assert (not (fp.isNaN ((_ to_fp 8 24) (_ bv2143289344 32)))))
(check-sat)
