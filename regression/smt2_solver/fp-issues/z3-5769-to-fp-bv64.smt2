; Z3#5769: to_fp from BV reinterpret cast on Float64
(set-logic QF_FP)
(declare-const bv (_ BitVec 64))
(assert (fp.isNormal ((_ to_fp 11 53) bv)))
(assert (fp.isPositive ((_ to_fp 11 53) bv)))
(check-sat)
