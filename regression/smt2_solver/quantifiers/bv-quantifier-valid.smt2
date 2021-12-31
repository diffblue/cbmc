(define-fun q1 () Bool (exists ((b (_ BitVec 8))) (= b #x00)))
(define-fun q2 () Bool (exists ((b (_ BitVec 8))) (not (= b #x00))))

(define-fun q3 () Bool (not (forall ((b (_ BitVec 8))) (= b #x00))))
(define-fun q4 () Bool (not (forall ((b (_ BitVec 8))) (not (= b #x00)))))

(define-fun q5 () Bool (exists ((a (_ BitVec 8)) (b (_ BitVec 8))) (= a b)))
(define-fun q6 () Bool (not (forall ((a (_ BitVec 8)) (b (_ BitVec 8))) (= a b))))

(define-fun q7 () Bool (forall ((a (_ BitVec 8))) (exists ((b (_ BitVec 8))) (= a b))))

; the above are all valid, and we assert one of them is not
(assert (not (and q1 q2 q3 q4 q5 q6 q7)))

(check-sat)
