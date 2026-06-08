; Regression for deferred bit-blasting dropping congruence axioms.
; Deferred assertions were replayed AFTER functions.finish_eager_conversion(),
; so an uninterpreted-function application occurring only in a deferred
; assertion (here m(zero_extend(x))) was registered too late to receive its
; congruence axioms, yielding spurious sat.
;
; UNSAT: assert 2 forces x = 0, so zero_extend(x) = 0 and by congruence
; m(zero_extend(x)) = m(0); assert 1 gives m(0) = 1 and assert 3 gives
; m(zero_extend(x)) = 0, a contradiction. Distilled (via ddsmt) from
; uninterpreted-functions/uf1. Expected: unsat (and without relying on
; DISABLE_DEFER_BITBLAST).
(set-logic QF_UFBV)
(declare-const x (_ BitVec 1))
(declare-fun m ((_ BitVec 32)) (_ BitVec 32))
(assert (= (_ bv1 32) (m (_ bv0 32))))
(assert (= (_ bv0 32) ((_ zero_extend 31) x)))
(assert (= (_ bv0 32) (m ((_ zero_extend 31) x))))
(check-sat)
