; CVC5#12335: A > 0, V > 0, A/V cannot be +0
(set-logic QF_FP)
(declare-const V (_ FloatingPoint 8 24))
(declare-const A (_ FloatingPoint 8 24))
(define-fun pz () (_ FloatingPoint 8 24) (fp #b0 #b00000000 #b00000000000000000000000))
(assert (fp.gt A pz))
(assert (fp.gt V pz))
(assert (fp.eq (fp.div RNE A V) pz))
(check-sat)
