; Based on Z3#7321, Z3#8169: fp.to_real is not supported by CBMC's SMT2 solver.
; This test documents the gap.

(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (= (fp.to_real x) 1.0))
(check-sat)
