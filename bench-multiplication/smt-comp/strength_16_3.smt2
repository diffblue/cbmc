(set-logic QF_BV)
; x * 3 == (x << 2) - x
(declare-fun x () (_ BitVec 16))
(assert (not (= (bvmul x (_ bv3 16)) (bvsub (bvshl x (_ bv2 16)) x))))
(check-sat)
