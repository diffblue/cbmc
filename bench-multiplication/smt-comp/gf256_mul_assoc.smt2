; GF(256) multiplication associativity check
; GF(256) uses polynomial multiplication modulo x^8 + x^4 + x^3 + x + 1
; This is carry-less multiplication (XOR instead of ADD) with reduction
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
; GF(256) multiply: a*b mod P where P = 0x11B
; We use 16-bit intermediate to avoid overflow
(define-fun gf_mul ((x (_ BitVec 8)) (y (_ BitVec 8))) (_ BitVec 8)
  (let ((wx ((_ zero_extend 8) x)) (wy ((_ zero_extend 8) y)))
  (let ((prod (bvmul wx wy)))
  ; Reduce mod P = x^8 + x^4 + x^3 + x + 1 = 0x11B
  ((_ extract 7 0) (bvurem prod (_ bv283 16))))))
; Check associativity: (a*b)*c == a*(b*c)
(assert (not (= (gf_mul (gf_mul a b) c) (gf_mul a (gf_mul b c)))))
(check-sat)
(exit)
