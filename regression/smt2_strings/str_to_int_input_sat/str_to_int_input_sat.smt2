(declare-const in String)
(assert (= (str.to.int in) 123))
(check-sat)
