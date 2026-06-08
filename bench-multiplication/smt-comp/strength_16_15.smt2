(set-logic QF_BV)
; x * 15 == (x << 4) - x
(declare-fun x () (_ BitVec 16))
(assert (not (= (bvmul x (_ bv15 16)) (bvsub (bvshl x (_ bv4 16)) x))))
(check-sat)
