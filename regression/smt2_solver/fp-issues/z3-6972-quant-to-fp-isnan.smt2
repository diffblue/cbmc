; Z3#6972: quantified formula with to_fp from BV and fp.isNaN
(set-logic FP)
(declare-fun bv () (_ BitVec 32))
(assert (forall ((x (_ BitVec 32)))
  (= (fp.isNaN ((_ to_fp 8 24) x))
     (fp.isNaN ((_ to_fp 8 24) bv)))))
(check-sat)
