(assert (str.in.re "abcdef" (re.* (re.range "a" "e"))))
(check-sat)
