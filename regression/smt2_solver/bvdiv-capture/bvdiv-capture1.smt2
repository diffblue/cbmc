; bvudiv must not capture a user symbol named "divisor"
(set-logic QF_BV)
(declare-const divisor (_ BitVec 8))
(declare-const r (_ BitVec 8))
(assert (= divisor #x06))
(assert (= r (bvudiv divisor #x02)))
(check-sat)
(get-value (r))
