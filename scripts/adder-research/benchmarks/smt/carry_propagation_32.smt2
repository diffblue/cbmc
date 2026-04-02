; SAT: overflow detection
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(assert (bvugt a #x7FFFFFFF))
(assert (bvugt b #x7FFFFFFF))
(assert (= ((_ extract 31 31) (bvadd a b)) ((_ extract 31 31) a)))
(check-sat)
(exit)
