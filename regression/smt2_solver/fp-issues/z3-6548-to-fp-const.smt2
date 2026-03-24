; Z3#6548: to_fp from constant real
(set-logic QF_FP)
(assert (fp.eq ((_ to_fp 8 24) RNE 3.14) ((_ to_fp 8 24) RNE 3.14)))
(check-sat)
