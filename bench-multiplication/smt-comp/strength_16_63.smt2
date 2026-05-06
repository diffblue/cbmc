(set-logic QF_BV)
; x * 63 == (x << 6) - x
(declare-fun x () (_ BitVec 16))
(assert (not (= (bvmul x (_ bv63 16)) (bvsub (bvshl x (_ bv6 16)) x))))
(check-sat)
