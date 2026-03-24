; Z3#8183: to_fp from large constant Real should produce infinity
(set-logic QF_FP)
(assert (not (fp.isInfinite ((_ to_fp 8 24) RNE 1e40))))
(check-sat)
