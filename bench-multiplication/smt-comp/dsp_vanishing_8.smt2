(set-logic QF_BV)
(declare-fun x () (_ BitVec 3))
(assert (not (= (bvadd (bvmul (_ bv4 3) (bvmul x x)) (bvmul (_ bv4 3) x)) (_ bv0 3))))
(check-sat)
