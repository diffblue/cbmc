; Z3#2631: quantified FPA formula - negation through to_fp roundtrip
; Should be unsat (neg(to_fp(bv(x))) always equals neg(to_fp(bv(c))) when x=c)
(set-logic FP)
(declare-fun c (_ FloatingPoint 8 24))
(assert (forall ((x (_ FloatingPoint 8 24)))
  (not (= (fp.neg x) (fp.neg c)))))
(check-sat)
