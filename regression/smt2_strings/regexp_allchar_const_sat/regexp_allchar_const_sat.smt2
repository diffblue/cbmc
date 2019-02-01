(assert (str.in.re "aaabbb" (re.++ (re.* (str.to.re "a")) (re.* re.allchar))))
(check-sat)
