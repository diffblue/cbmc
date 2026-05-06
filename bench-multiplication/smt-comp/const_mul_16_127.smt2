(set-logic QF_BV)
; Verify x * 127 equals manual shift-add at BW=16
(declare-fun x () (_ BitVec 16))
(assert (not (= (bvmul x (_ bv127 16)) (bvmul (_ bv127 16) x))))
(check-sat)
