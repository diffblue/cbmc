; CVC5#12371, quantifier-free variant of cvc5-12371-quant-to-fp-real: the
; instance x = 1e40 rounds to +oo in Float32, and 0 >= 1e40 is false.
(set-logic QF_FPLRA)
(declare-const x Real)
(assert (= x 10000000000000000000000000000000000000000.0))
(assert (>= 0.0 (ite (fp.isInfinite ((_ to_fp 8 24) RNE x)) x 0.0)))
(check-sat)
