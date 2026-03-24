; Z3#2631: negation is self-inverse: neg(neg(x)) == x
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (not (= (fp.neg (fp.neg x)) x)))
(check-sat)
