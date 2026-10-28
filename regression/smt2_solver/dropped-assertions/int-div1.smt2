; integer division is not supported; must not answer sat
(set-logic QF_LIA)
(assert (not (= (div (- 7) 2) (- 4))))
(check-sat)
