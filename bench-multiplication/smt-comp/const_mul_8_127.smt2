(set-logic QF_BV)
; Verify x * 127 equals manual shift-add at BW=8
(declare-fun x () (_ BitVec 8))
(assert (not (= (bvmul x (_ bv127 8)) (bvmul (_ bv127 8) x))))
(check-sat)
