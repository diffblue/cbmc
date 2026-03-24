; Z3#4880: forall a. not(isNegative(fp.min(a, +0))) should be unsat
; fp.min unsupported
(set-logic FP)
(assert (forall ((a (_ FloatingPoint 8 24)))
  (not (fp.isNegative (fp.min a (_ +zero 8 24))))))
(check-sat)
