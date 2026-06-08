; Addition/subtraction cancellation: a + b - b == a
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(assert (not (= (bvsub (bvadd a b) b) a)))
(check-sat)
(exit)
