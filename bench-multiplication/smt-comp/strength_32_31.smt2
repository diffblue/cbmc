(set-logic QF_BV)
; x * 31 == (x << 5) - x
(declare-fun x () (_ BitVec 32))
(assert (not (= (bvmul x (_ bv31 32)) (bvsub (bvshl x (_ bv5 32)) x))))
(check-sat)
