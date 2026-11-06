; extract with indices beyond operand width must be rejected
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= ((_ extract 5 4) x) #b11))
(check-sat)
