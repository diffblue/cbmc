(assert (str.in.re "e" (re.inter (re.range "a" "b") (re.range "b" "w"))))
(check-sat)
