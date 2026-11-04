; chained = is not supported; must not answer sat
(set-logic QF_BV)
(assert (= #x01 #x01 #x02))
(check-sat)
