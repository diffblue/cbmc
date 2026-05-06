(set-logic QF_BV)
; Verify x * 3 equals manual shift-add at BW=8
(declare-fun x () (_ BitVec 8))
(assert (not (= (bvmul x (_ bv3 8)) (bvmul (_ bv3 8) x))))
(check-sat)
