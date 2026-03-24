; Based on Z3#6728: NaN equality with uninterpreted functions
; In SMT-LIB, (= NaN NaN) is true (structural equality).
; If (= t1 t2) is true, then (= (f t1) (f t2)) must also be true
; for any uninterpreted function f (congruence).
; This test checks that the solver handles NaN correctly through UFs.

(set-logic QF_FPUF)
(declare-const x (_ FloatingPoint 8 24))
(declare-fun f ((_ FloatingPoint 8 24)) (_ FloatingPoint 8 24))

; fp.add of anything with NaN is NaN
; Both sides produce NaN, so they are equal (structural =)
; Therefore f applied to both must also be equal
(assert (not (= (f (fp.add RNE x (_ NaN 8 24)))
              (f (fp.add RNE (_ NaN 8 24) x)))))
(check-sat)
