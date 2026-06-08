(set-logic QF_BV)
; x * 63 == (x << 6) - x
(declare-fun x () (_ BitVec 32))
(assert (not (= (bvmul x (_ bv63 32)) (bvsub (bvshl x (_ bv6 32)) x))))
(check-sat)
