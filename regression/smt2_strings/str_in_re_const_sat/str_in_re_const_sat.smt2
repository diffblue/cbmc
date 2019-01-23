(assert (str.in.re "abcdef" (re.* (re.range "a" "f"))))
(check-sat)
