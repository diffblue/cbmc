; CVC5#12387: fp.eq is symmetric
(set-logic QF_FP)
(declare-const x Bool)
(declare-const o (_ FloatingPoint 8 24))
(define-fun v1 () (_ FloatingPoint 8 24) (ite x o (_ NaN 8 24)))
(define-fun v2 () (_ FloatingPoint 8 24) (_ -oo 8 24))
(assert (fp.eq v1 v2))
(assert (not (fp.eq v2 v1)))
(check-sat)
