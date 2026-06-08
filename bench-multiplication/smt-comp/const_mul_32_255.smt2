(set-logic QF_BV)
; Verify x * 255 equals manual shift-add at BW=32
(declare-fun x () (_ BitVec 32))
(assert (not (= (bvmul x (_ bv255 32)) (bvmul (_ bv255 32) x))))
(check-sat)
