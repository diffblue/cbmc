(assert (str.in.re "aaac" (re.++ (re.+ (str.to.re "a")) (re.opt (str.to.re "b")))))
(check-sat)
