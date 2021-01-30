(set-logic QF_UFBV)

(declare-fun myfun ((_ BitVec 32)) (_ BitVec 32))

(assert (= (myfun (_ bv10 32)) (_ bv20 32)))

(declare-const x (_ BitVec 32))
(assert (= x (_ bv10 32)))
(assert (= (myfun x) (_ bv30 32)))

(check-sat)
