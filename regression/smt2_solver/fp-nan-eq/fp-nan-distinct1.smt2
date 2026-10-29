; Two NaN bit patterns are not distinct under SMT-LIB distinct
(set-logic QF_BVFP)
(assert (distinct ((_ to_fp 8 24) #x7fc00000) ((_ to_fp 8 24) #x7fc00001)))
(check-sat)
