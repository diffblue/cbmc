; Based on Z3#7162: fp.sub with RNA rounding on Float64
; The original issue involves fp.fma (not supported by CBMC's SMT2 solver),
; so this is a simplified version testing fp.sub with RNA rounding.
; The assertion says: a4 - (a3 * a1 + a0) == +0.0
; Simplified to just test fp.sub RNA produces valid results.

(set-logic QF_FP)
(declare-const a (_ FloatingPoint 11 53))
(declare-const b (_ FloatingPoint 11 53))

; fp.sub RNA a b == +0.0 should be satisfiable (e.g., a == b)
(assert (= (fp.sub RNA a b)
  (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)))
(check-sat)
