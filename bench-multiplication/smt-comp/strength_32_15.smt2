(set-logic QF_BV)
; x * 15 == (x << 4) - x
(declare-fun x () (_ BitVec 32))
(assert (not (= (bvmul x (_ bv15 32)) (bvsub (bvshl x (_ bv4 32)) x))))
(check-sat)
