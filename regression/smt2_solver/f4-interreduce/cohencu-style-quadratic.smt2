; F4 interreduction regression test: distilled from
; cohencu_2/3 in the SMT-COMP sample. The IF-condition is
; quadratic in z (z*z), creating a Rabinowitsch polynomial
; whose refutation requires reducing a non-leading term.
;
; Without F4-style tail reduction (interreduce_basis):
;   T/O at bw=32 within 30s.
; With F4 (default):
;   refutes in <5s at bw=32.
(set-logic QF_BV)
(declare-const n (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-const z (_ BitVec 32))
(assert (= (bvadd z y)
   (bvadd (_ bv7 32) (bvmul (_ bv3 32) (bvmul n n)) (bvmul (_ bv9 32) n))))
(assert (= y (bvadd (bvmul (_ bv3 32) n) (bvmul (_ bv3 32) (bvmul n n)) (_ bv1 32))))
(assert (not (= (bvadd (bvmul z z) (_ bv12 32))
                 (bvadd (bvmul (_ bv6 32) z) (bvmul (_ bv12 32) y)))))
(check-sat)
(exit)
