(assert (str.in.re "aaabbbc" (re.++ (re.* (str.to.re "a")) (re.* (str.to.re "b")))))
(check-sat)
