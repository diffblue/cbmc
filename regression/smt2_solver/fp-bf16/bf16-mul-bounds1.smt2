; Based on CVC5#12306: BF16 multiplication with bound checking.
; c * x * x should produce consistent results regardless of
; the order of bound checks in an OR.

(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 8))
(declare-const c (_ FloatingPoint 8 8))

; c * x * x
(define-fun cxx () (_ FloatingPoint 8 8)
  (fp.mul RNE (fp.mul RNE c x) x))

; Some bound value
(define-fun bound () (_ FloatingPoint 8 8)
  (fp #b0 #b10000010 #b0000000))

; Check: (fp.gt cxx bound) or (fp.lt cxx (fp.neg bound))
; should be the same as
; (fp.lt cxx (fp.neg bound)) or (fp.gt cxx bound)
(assert (not (= (or (fp.gt cxx bound) (fp.lt cxx (fp.neg bound)))
               (or (fp.lt cxx (fp.neg bound)) (fp.gt cxx bound)))))
(check-sat)
