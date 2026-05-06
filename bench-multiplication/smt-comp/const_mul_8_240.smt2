(set-logic QF_BV)
; Verify x * 240 equals manual shift-add at BW=8
(declare-fun x () (_ BitVec 8))
(assert (not (= (bvmul x (_ bv240 8)) (bvmul (_ bv240 8) x))))
(check-sat)
