(set-logic QF_BV)

; the quantified identifiers are in a separate scope
(define-fun q1 () Bool (exists ((a Bool)) a))
(declare-const a (_ BitVec 32))
(assert (not (= a a)))

; declare-const first
(declare-const b (_ BitVec 32))
(define-fun q2 () Bool (exists ((b Bool)) b))

(check-sat)
