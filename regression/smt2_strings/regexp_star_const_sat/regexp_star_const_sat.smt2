(assert (str.in.re "aaabbb" (re.++ (re.* (str.to.re "a")) (re.* (str.to.re "b")))))
(check-sat)
