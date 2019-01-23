(assert (str.in.re "abcd" (re.union (str.to.re "ab") (str.to.re "cd"))))
(check-sat)
