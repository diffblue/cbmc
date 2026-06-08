; Item 6 from doc/paper-algebraic/remaining-work.md regression test:
; 64-bit overflow check via high-half-of-product extraction.
;
; UNSAT because a, b <= 10^9 implies a*b <= 10^18 < 2^60 < 2^64,
; so the high half (extract 127 64) of the zext-product is 0.
;
; Without the Item 6 guard, the algebraic pipeline pushes the
; disequality (containing the non-zero-LO extract) to
; algebraic_disequalities, then spends ~4 s on bit-chain
; predicate encoding before the main_gb loop discovers there's
; no polynomial constraint to refute. With the guard, the
; disequality is correctly recognised as non-polynomial and
; bit-blasting handles the formula in <0.05 s.
(set-logic QF_BV)
(declare-const a (_ BitVec 64))
(declare-const b (_ BitVec 64))
(assert (bvule a (_ bv1000000000 64)))
(assert (bvule b (_ bv1000000000 64)))
(assert (not (= ((_ extract 127 64) (bvmul (concat (_ bv0 64) a) (concat (_ bv0 64) b))) (_ bv0 64))))
(check-sat)
(exit)
