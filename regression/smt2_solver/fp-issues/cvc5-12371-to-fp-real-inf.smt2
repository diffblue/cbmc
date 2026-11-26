; CVC5#12371: to_fp from large constant Real overflows to infinity
(set-logic QF_FP)
(assert (fp.isInfinite ((_ to_fp 8 24) RNE 10000000000000000000000000000000000000000.0)))
(assert (fp.isPositive ((_ to_fp 8 24) RNE 10000000000000000000000000000000000000000.0)))
(check-sat)
