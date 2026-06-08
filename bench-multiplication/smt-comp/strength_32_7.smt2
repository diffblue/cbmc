(set-logic QF_BV)
; x * 7 == (x << 3) - x
(declare-fun x () (_ BitVec 32))
(assert (not (= (bvmul x (_ bv7 32)) (bvsub (bvshl x (_ bv3 32)) x))))
(check-sat)
