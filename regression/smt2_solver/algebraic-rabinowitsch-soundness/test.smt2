(set-logic QF_BV)
; Item 14 soundness regression: the algebraic pre-solver must NOT
; report unsat here. The two products differ by the nonzero, NON-UNIT
; constant 2 (= -2 mod 16), so the disequality is always true and the
; formula is SAT. The previously-used Rabinowitsch unit-trick encoded
; "diff != 0" as "2*e - 1 = 0", which is unsatisfiable over Z_{2^4}
; (2 is not invertible), and so wrongly concluded unsat. The sound
; ideal-membership / vanishing refutation correctly declines to refute
; (2 is a nonzero constant, not in the ideal of the equalities).
(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))
(assert (not (= (bvmul a b) (bvadd (bvmul b a) (_ bv2 4)))))
(check-sat)
