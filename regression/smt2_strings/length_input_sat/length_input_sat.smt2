(declare-const str String)
(assert (= (str.len str) 3))
(check-sat)
