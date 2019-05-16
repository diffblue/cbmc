(set-logic LIA)

(define-fun next ((x Int)) Int x )
(assert (= (next ) 243))

(check-sat)
