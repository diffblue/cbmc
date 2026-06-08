; Verify: (a*a) mod m == ((a mod m) * (a mod m)) mod m
; This is a key property for modular exponentiation
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun m () (_ BitVec 16))
(assert (not (= (_ bv0 16) m)))
(assert (not (= (bvurem (bvmul a a) m) (bvurem (bvmul (bvurem a m) (bvurem a m)) m))))
(check-sat)
(exit)
