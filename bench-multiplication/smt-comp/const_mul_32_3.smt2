(set-logic QF_BV)
; Verify x * 3 equals manual shift-add at BW=32
(declare-fun x () (_ BitVec 32))
(assert (not (= (bvmul x (_ bv3 32)) (bvmul (_ bv3 32) x))))
(check-sat)
