; Z3#6972, quantifier-free variant of z3-6972-quant-to-fp-isnan: the
; instances x = 0x7FC00000 (a NaN) and x = 0x00000000 (+0) cannot both have
; the same fp.isNaN value as to_fp(bv).
(set-logic QF_BVFP)
(declare-fun bv () (_ BitVec 32))
(assert (= (fp.isNaN ((_ to_fp 8 24) #x7FC00000))
           (fp.isNaN ((_ to_fp 8 24) bv))))
(assert (= (fp.isNaN ((_ to_fp 8 24) #x00000000))
           (fp.isNaN ((_ to_fp 8 24) bv))))
(check-sat)
