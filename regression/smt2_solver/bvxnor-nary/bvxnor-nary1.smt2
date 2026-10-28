; n-ary bvxnor must be left-associative
(set-logic QF_BV)
(assert (= (bvxnor #b0 #b0 #b0) (bvxnor (bvxnor #b0 #b0) #b0)))
(check-sat)
