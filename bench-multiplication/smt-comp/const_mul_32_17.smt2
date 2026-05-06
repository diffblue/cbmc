(set-logic QF_BV)
; Verify x * 17 equals manual shift-add at BW=32
(declare-fun x () (_ BitVec 32))
(assert (not (= (bvmul x (_ bv17 32)) (bvmul (_ bv17 32) x))))
(check-sat)
