(set-logic QF_BV)
; Verify x * 85 equals manual shift-add at BW=8
(declare-fun x () (_ BitVec 8))
(assert (not (= (bvmul x (_ bv85 8)) (bvmul (_ bv85 8) x))))
(check-sat)
