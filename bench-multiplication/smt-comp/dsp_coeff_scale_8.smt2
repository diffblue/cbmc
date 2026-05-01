(set-logic QF_BV)
; 128*x^2 + 128*x vanishes mod 256 (8-bit) since 128 = 2^7 and x(x-1) is always even
(declare-fun x () (_ BitVec 8))
(assert (not (= (bvadd (bvmul (_ bv128 8) (bvmul x x)) (bvmul (_ bv128 8) x)) (_ bv0 8))))
(check-sat)
