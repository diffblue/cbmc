; Based on CVC5#12306: OR commutativity in BF16.
; (or A B) should be equivalent to (or B A).
; Test with FP bound checks on BF16 (_ FloatingPoint 8 8).

(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 8))
(declare-const c (_ FloatingPoint 8 8))

; Some bound: x in [-5.87, -5.87 + 0.04]
; -5.87 in BF16 ≈ fp #b1 #b10000001 #b0111100
; -5.83 in BF16 ≈ fp #b1 #b10000001 #b0111010
(define-fun lo () (_ FloatingPoint 8 8)
  (fp #b1 #b10000001 #b0111100))
(define-fun hi () (_ FloatingPoint 8 8)
  (fp #b1 #b10000001 #b0111010))

(define-fun bound_a () Bool (fp.geq x lo))
(define-fun bound_b () Bool (fp.leq x hi))

; (or bound_a bound_b) should equal (or bound_b bound_a)
(assert (not (= (or bound_a bound_b) (or bound_b bound_a))))
(check-sat)
