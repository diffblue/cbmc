(assert (str.in.re "ab" (re.union (str.to.re "ab") (str.to.re "cd"))))
(check-sat)
