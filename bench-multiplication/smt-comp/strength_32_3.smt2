(set-logic QF_BV)
; x * 3 == (x << 2) - x
(declare-fun x () (_ BitVec 32))
(assert (not (= (bvmul x (_ bv3 32)) (bvsub (bvshl x (_ bv2 32)) x))))
(check-sat)
