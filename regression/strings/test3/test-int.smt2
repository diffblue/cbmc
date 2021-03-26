(set-option :produce-models true)
(set-logic ALL)

(declare-fun s () String)
(declare-fun s2 () String)
(declare-fun s3 () String)

(declare-fun i () Int)

(assert (= s (str.++ s2 s3)))

(assert (= (str.len s2) i))
(assert (= s3 "pippo"))

(define-fun p1 () Bool (= (str.len s) (+ i 5)))
(define-fun p2 () Bool (str.suffixof "po" s))
(define-fun p3 () Bool (= (str.at s i) "p"))

(assert (or (not p1) (not p2) (not p3)))
(check-sat)
