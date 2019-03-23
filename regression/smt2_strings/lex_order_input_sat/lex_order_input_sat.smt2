(declare-const in String)
(assert (> (str.len in) 1))
(assert (str.< in "acc"))
(check-sat)
