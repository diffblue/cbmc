; n-ary bvnand must be rejected
(set-logic QF_BV)
(assert (= (bvnand #b0 #b0 #b0) #b0))
(check-sat)
