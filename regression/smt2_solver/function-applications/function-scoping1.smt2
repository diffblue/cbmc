(set-logic QF_BV)

; the function parameters are in a separate scope

(define-fun min ((a (_ BitVec 8)) (b (_ BitVec 8))) (_ BitVec 8)
    (ite (bvule a b) a b))

(declare-const a (_ BitVec 32))

(assert (not (= a a)))

(check-sat)
