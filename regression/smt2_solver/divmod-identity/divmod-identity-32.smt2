; Phase A.3 regression test: div/mod identity at 32-bit.
; UNSAT because (a/b)*b + (a%b) == a holds for all a, b in
; SMT-LIB semantics (with bvurem b 0 = b, bvudiv b 0 = ~0).
; Without the Phase A.3 nonzero fast-path, this benchmark T/Os
; at 30s. With the fast-path, it solves in <0.1s.
(set-logic QF_BV)
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(assert (bvult (_ bv0 32) b))
(assert (not (= a (bvadd (bvmul (bvudiv a b) b) (bvurem a b)))))
(check-sat)
(exit)
