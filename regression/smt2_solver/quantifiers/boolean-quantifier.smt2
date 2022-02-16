(define-fun q1 () Bool (exists ((b Bool)) b))
(define-fun q2 () Bool (exists ((b Bool)) (not b)))

(define-fun q3 () Bool (not (forall ((b Bool)) b)))
(define-fun q4 () Bool (not (forall ((b Bool)) (not b))))

(define-fun q5 () Bool (exists ((a Bool) (b Bool)) (= a b)))
(define-fun q6 () Bool (not (forall ((a Bool) (b Bool)) (= a b))))

(define-fun q7 () Bool (forall ((a Bool)) (exists ((b Bool)) (= a b))))

; the above are all valid, and we assert one of them is not
(assert (not (and q1 q2 q3 q4 q5 q6 q7)))

(check-sat)
