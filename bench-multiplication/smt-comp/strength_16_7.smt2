(set-logic QF_BV)
; x * 7 == (x << 3) - x
(declare-fun x () (_ BitVec 16))
(assert (not (= (bvmul x (_ bv7 16)) (bvsub (bvshl x (_ bv3 16)) x))))
(check-sat)
