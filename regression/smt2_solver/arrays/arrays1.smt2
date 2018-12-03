(set-logic QF_ABV)

(declare-const array1 (Array (_ BitVec 16) (_ BitVec 8)))
(define-const array2 (Array (_ BitVec 16) (_ BitVec 8)) (store array1 #x0001 #x10))
(define-const array3 (Array (_ BitVec 16) (_ BitVec 8)) ((as const (Array (_ BitVec 16) (_ BitVec 8))) #xff))

(check-sat)
(get-value (array2))
(get-value (array3))
