(declare-const str String)
(assert (= (str.len str) 3))
(assert (= (str.len str) 2))
(check-sat)
