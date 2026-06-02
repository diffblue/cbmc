; F4 interreduction regression test: distilled from
; cohencu_2/3 in the SMT-COMP sample. The IF-condition is
; quadratic in z (z*z); refuting the disequality requires
; reducing a non-leading term (F4-style tail reduction in
; interreduce_basis).
;
; The disequality is genuinely UNSAT: substituting the two
; equality constraints gives z = 6 + 6n and y = 1 + 3n + 3n^2,
; under which (z*z + 12) - (6*z + 12*y) vanishes identically, so
; the third assertion (the negation) is unsatisfiable. Confirmed
; unsat by z3 and cvc5 at this bitwidth.
;
; Disequalities use Song et al.'s sound z*(a-b) - 2^{d-1} = 0
; encoding (NOT the textbook Rabinowitsch unit-trick, which is
; unsound over Z_{2^d}). With that sound encoding the refutation
; completes quickly at bw=16; at bw=32 it exceeds the regression
; budget (a known completeness limitation of the sound encoding
; relative to the earlier unsound shortcut), so this test uses
; bw=16 to keep deterministic, oracle-verified coverage of the
; F4 tail-reduction path.
(set-logic QF_BV)
(declare-const n (_ BitVec 16))
(declare-const y (_ BitVec 16))
(declare-const z (_ BitVec 16))
(assert (= (bvadd z y)
   (bvadd (_ bv7 16) (bvmul (_ bv3 16) (bvmul n n)) (bvmul (_ bv9 16) n))))
(assert (= y (bvadd (bvmul (_ bv3 16) n) (bvmul (_ bv3 16) (bvmul n n)) (_ bv1 16))))
(assert (not (= (bvadd (bvmul z z) (_ bv12 16))
                 (bvadd (bvmul (_ bv6 16) z) (bvmul (_ bv12 16) y)))))
(check-sat)
(exit)
