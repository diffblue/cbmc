(set-logic QF_BV)

; the range type doesn't match!
(define-fun min ((a (_ BitVec 8)) (b (_ BitVec 8))) (_ BitVec 16)
    (ite (bvule a b) a b))

(define-fun p1 () Bool (= (min #x01 #x02) #x01))
(define-fun p2 () Bool (= (min #xff #xfe) #xfe))

; all must be true

(assert (not (and p1 p2)))

(check-sat)
