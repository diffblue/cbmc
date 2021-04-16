(declare-fun a () Bool)
(declare-fun b () Bool)
(define-fun c () Bool (and a b))

(assert c)

(check-sat-assuming ((not a)))
