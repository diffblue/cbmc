; Based on Z3#8414: fp.rem on non-standard FP sort (_ FloatingPoint 1 37).
; Z3 crashes with assertion violation in mpf.cpp.
; Test that CBMC handles this without crashing.

(set-logic QF_FP)
(assert (fp.isZero (fp.rem
  (fp (_ bv0 1) #b111100110000111111100101110000000011 (_ bv0 1))
  (fp (_ bv0 1) (_ bv1 36) (_ bv0 1)))))
(check-sat)
