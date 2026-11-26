; Two NaN bit patterns are equal under SMT-LIB =
(set-logic QF_BVFP)
(assert (not (= ((_ to_fp 8 24) #x7fc00000) ((_ to_fp 8 24) #x7fc00001))))
(check-sat)
