; Z3#4880: forall a. not(isNegative(fp.min(a, +0))) should be unsat
; because fp.min(-0, +0) = -0 which IS negative
(set-logic FP)
(assert (forall ((a (_ FloatingPoint 8 24)))
  (not (fp.isNegative (fp.min a (fp #b0 #b00000000 #b00000000000000000000000))))))
(check-sat)
