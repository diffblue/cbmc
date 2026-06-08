; Regression for the unsound "adjacent equality implications" clause that
; was added to bv_utilst::equal() (commit d06d50c678) and removed again.
; That optimisation added (eq[i] OR eq[i+1]) for 10-13 bit equality checks,
; wrongly asserting that two adjacent equality bits can never both differ.
; It made satisfiable formulas with such equality checks spuriously UNSAT.
;
; Here x = 0 != 3, so the ite takes the else branch zero_extend(b), and
; 0 = zero_extend(b) is satisfiable with b = 0. Distilled (via ddsmt) from
; mcm/06 in SMT-COMP QF_BV. Expected: sat.
(set-logic QF_BV)
(declare-const b (_ BitVec 1))
(define-fun x () (_ BitVec 11) (_ bv0 11))
(assert (= (_ bv0 11) (ite (= x (_ bv3 11)) (_ bv0 11) ((_ zero_extend 10) b))))
(check-sat)
