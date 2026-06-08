(set-logic QF_BV)
; x * 31 == (x << 5) - x
(declare-fun x () (_ BitVec 16))
(assert (not (= (bvmul x (_ bv31 16)) (bvsub (bvshl x (_ bv5 16)) x))))
(check-sat)
