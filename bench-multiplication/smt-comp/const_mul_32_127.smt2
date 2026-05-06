(set-logic QF_BV)
; Verify x * 127 equals manual shift-add at BW=32
(declare-fun x () (_ BitVec 32))
(assert (not (= (bvmul x (_ bv127 32)) (bvmul (_ bv127 32) x))))
(check-sat)
