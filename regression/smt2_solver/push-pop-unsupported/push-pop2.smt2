; a sat answer remains valid even when pop is not supported
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(push 1)
(assert (= x #x01))
(pop 1)
(check-sat)
