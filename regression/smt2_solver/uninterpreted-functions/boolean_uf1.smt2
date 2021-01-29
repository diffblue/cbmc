(set-logic QF_UFBV)

(declare-fun myfun ((_ BitVec 32)) Bool)

(assert (myfun (_ bv10 32)))

(declare-const x (_ BitVec 32))
(assert (= x (_ bv10 32)))
(assert (not (myfun x)))

(check-sat)
