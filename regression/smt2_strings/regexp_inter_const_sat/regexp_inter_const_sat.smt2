(assert (str.in.re "e" (re.inter (re.range "a" "h") (re.range "d" "w"))))
(check-sat)
