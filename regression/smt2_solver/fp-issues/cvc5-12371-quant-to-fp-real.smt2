; CVC5#12371: quantified formula with to_fp from Real
; forall x: 0 >= ite(isInfinite(to_fp(x)), x, 0)
; This should be unsat (counterexample: x = -1e40)
(set-logic ALL)
(assert (forall ((x Real))
  (>= 0.0 (ite (fp.isInfinite ((_ to_fp 8 24) RNE x)) x 0.0))))
(check-sat)
