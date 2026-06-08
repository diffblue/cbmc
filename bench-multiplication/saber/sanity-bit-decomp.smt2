; Sanity check for future direction (4): bit-decomposition variables.
;
; Test: does Buchberger terminate when we add idempotency
; b_i^2 = b_i and sum-decomposition constraints to a small
; commutativity benchmark?
;
; Working in Z_{2^8}, with 4-bit "decomposed" inputs.
; Each input a, b is decomposed into bits a0..a3 (and b0..b3),
; each in {0,1}. We assert commutativity of a*b.
;
; Polynomial system (interpreted in Z_{2^8}):
;   a_i^2 = a_i           (8 idempotency equations)
;   b_i^2 = b_i
;   a = a0 + 2 a1 + 4 a2 + 8 a3      (1 sum-decomposition)
;   b = b0 + 2 b1 + 4 b2 + 8 b3      (1 sum-decomposition)
; Goal:
;   forall a0..a3, b0..b3 satisfying above.   a*b == b*a
;
; Question: does Buchberger terminate in reasonable time on this
; augmented system, or does the addition of idempotency
; constraints cause an explosion?

(set-logic QF_BV)

(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))

; bit-decomposition variables (logically in {0,1}, but stored in 8-bit)
(declare-const a0 (_ BitVec 8))
(declare-const a1 (_ BitVec 8))
(declare-const a2 (_ BitVec 8))
(declare-const a3 (_ BitVec 8))
(declare-const b0 (_ BitVec 8))
(declare-const b1 (_ BitVec 8))
(declare-const b2 (_ BitVec 8))
(declare-const b3 (_ BitVec 8))

; idempotency: a_i^2 = a_i forces a_i in {0,1} (since gcd(a_i, a_i-1)=1)
(assert (= (bvmul a0 a0) a0))
(assert (= (bvmul a1 a1) a1))
(assert (= (bvmul a2 a2) a2))
(assert (= (bvmul a3 a3) a3))
(assert (= (bvmul b0 b0) b0))
(assert (= (bvmul b1 b1) b1))
(assert (= (bvmul b2 b2) b2))
(assert (= (bvmul b3 b3) b3))

; sum-decomposition: a = sum_i 2^i a_i (only 4 bits, so a < 16)
(assert (= a (bvadd a0
              (bvadd (bvmul (_ bv2 8) a1)
              (bvadd (bvmul (_ bv4 8) a2)
                     (bvmul (_ bv8 8) a3))))))
(assert (= b (bvadd b0
              (bvadd (bvmul (_ bv2 8) b1)
              (bvadd (bvmul (_ bv4 8) b2)
                     (bvmul (_ bv8 8) b3))))))

; goal: commutativity of a*b
(assert (distinct (bvmul a b) (bvmul b a)))
(check-sat)
