; Z3#8097: UF with FP arguments
(set-logic QF_FPUF)
(declare-fun f ((_ FloatingPoint 8 24) (_ FloatingPoint 8 24)) (_ FloatingPoint 8 24))
(declare-const x (_ FloatingPoint 8 24))
(define-fun pz () (_ FloatingPoint 8 24) (fp #b0 #b00000000 #b00000000000000000000000))
(assert (fp.eq (f x pz) pz))
(check-sat)
