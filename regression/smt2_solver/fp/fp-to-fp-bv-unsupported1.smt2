; Based on Z3#5769, Z3#6079: to_fp from bitvector (reinterpret cast).
; CBMC's SMT2 solver does not support ((_ to_fp eb sb) bv) where bv
; is a bitvector. This is the IEEE 754 bit reinterpretation.

(set-logic QF_FP)
(declare-const bv (_ BitVec 32))
(declare-const f (_ FloatingPoint 8 24))
(assert (= f ((_ to_fp 8 24) bv)))
(assert (fp.eq f (fp #b0 #b01111111 #b00000000000000000000000)))
(check-sat)
