(set-logic QF_BV)

; the let parameters are in a separate scope
(define-fun let1 () Bool (let ((a true)) a))
(declare-const a (_ BitVec 32))
(assert (not (= a a)))

; declare-const first
(declare-const b (_ BitVec 32))
(define-fun let2 () Bool (let ((b true)) b))

(check-sat)
