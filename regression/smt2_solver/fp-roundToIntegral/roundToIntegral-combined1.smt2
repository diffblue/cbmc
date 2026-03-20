; Based on Z3#4841: Combined fp.add, fp.div, fp.roundToIntegral on
; non-standard sort (_ FloatingPoint 2 6).
; X = Y+Z = Y/Z = roundToIntegral(RTZ, Y), Y != Z.
; Z3 produced an invalid model for this. CBMC also produces an invalid
; model due to the roundToIntegral bug on non-standard sorts.

(set-logic QF_FP)
(declare-fun X () (_ FloatingPoint 2 6))
(declare-fun Y () (_ FloatingPoint 2 6))
(declare-fun Z () (_ FloatingPoint 2 6))
(assert (and (= X (fp.add RTZ Y Z))
             (= X (fp.div RTZ Y Z))
             (= X (fp.roundToIntegral RTZ Y))
             (not (= Y Z))))
(check-sat)
