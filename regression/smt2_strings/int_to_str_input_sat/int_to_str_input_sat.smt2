(declare-const str String)
(declare-const number Int)
(assert (= (int.to.str number) str))
(check-sat)
