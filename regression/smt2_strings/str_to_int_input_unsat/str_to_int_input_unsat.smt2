(declare-const in String)
(assert (= (str.to.int in) 123))
(assert (= (str.to.int in) 1234))
(check-sat)
