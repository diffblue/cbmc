(assert (str.in.re "aaa" (re.++ (re.+ (str.to.re "a")) (re.+ (str.to.re "b")))))
(check-sat)
