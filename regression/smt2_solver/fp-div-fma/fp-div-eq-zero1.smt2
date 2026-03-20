; Based on CVC5#12335: fp.div RNE with fp.eq and fp.gt on Float32.
; Quantifier-free version of the CVC5 issue.
; If a >= +0 and V < x and A > +0 and A/V == +0, find a contradiction.

(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const a (_ FloatingPoint 8 24))
(declare-const V (_ FloatingPoint 8 24))
(declare-const A (_ FloatingPoint 8 24))

(define-fun pzero () (_ FloatingPoint 8 24)
  (fp #b0 #b00000000 #b00000000000000000000000))

(assert (fp.lt V x))
(assert (fp.eq a a))
(assert (fp.gt A pzero))
(assert (fp.eq (fp.div RNE A V) pzero))
(assert (fp.geq a pzero))
(check-sat)
