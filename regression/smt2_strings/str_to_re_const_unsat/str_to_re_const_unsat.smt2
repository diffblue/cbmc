(assert (str.in.re "abba" (re.* (re.union (str.to.re "a") (str.to.re "c")))))
(check-sat)
