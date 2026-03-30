; Z3#6970: to_fp from BV with fp.leq and bvxnor
(set-logic QF_FP)
(declare-fun bv () (_ BitVec 32))
(assert (fp.leq ((_ to_fp 8 24) bv) (fp #b0 #b00000000 #b00000000000000000000000)))
(assert (not (fp.geq ((_ to_fp 8 24) (bvxnor (_ bv0 32) bv)) (fp #b0 #b00000000 #b00000000000000000000000))))
(check-sat)
