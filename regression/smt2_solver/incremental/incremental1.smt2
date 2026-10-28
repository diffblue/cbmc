; assert after check-sat must not crash
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(assert (= y (bvadd x #x1)))
(check-sat)
(assert (= x #x3))
(assert (not (= y #x4)))
(check-sat)
