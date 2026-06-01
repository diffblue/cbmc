; Phase A.3 extension regression test: div/mod identity at 32-bit
; with the constraint b != ~0 (encoded as bvult b ~0).
; UNSAT because (a/b)*b + (a%b) == a holds for all a, b in
; SMT-LIB semantics.
;
; This benchmark exercises the x != ~0 pattern of the extended
; nonzero fast-path (Item 2 in remaining-work.md).
; Without the extension, this benchmark T/Os at 30s; with the
; extension, it solves in <0.05s.
(set-logic QF_BV)
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(assert (bvult b #xffffffff))
(assert (not (= a (bvadd (bvmul (bvudiv a b) b) (bvurem a b)))))
(check-sat)
(exit)
