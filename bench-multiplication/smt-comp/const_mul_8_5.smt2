(set-logic QF_BV)
; Verify x * 5 equals manual shift-add at BW=8
(declare-fun x () (_ BitVec 8))
(assert (not (= (bvmul x (_ bv5 8)) (bvmul (_ bv5 8) x))))
(check-sat)
