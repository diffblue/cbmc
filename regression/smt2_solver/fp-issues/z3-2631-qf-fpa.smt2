; Z3#2631, quantifier-free variant of z3-2631-quant-fpa: instantiating the
; quantified variable x with c refutes forall x. fp.neg(x) != fp.neg(c).
(set-logic QF_FP)
(declare-const c (_ FloatingPoint 8 24))
(declare-const x (_ FloatingPoint 8 24))
(assert (= x c))
(assert (not (= (fp.neg x) (fp.neg c))))
(check-sat)
