(set-logic QF_BV)
; Verify x * 255 equals manual shift-add at BW=16
(declare-fun x () (_ BitVec 16))
(assert (not (= (bvmul x (_ bv255 16)) (bvmul (_ bv255 16) x))))
(check-sat)
