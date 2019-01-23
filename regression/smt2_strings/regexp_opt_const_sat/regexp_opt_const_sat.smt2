(assert (str.in.re "aaab" (re.++ (re.+ (str.to.re "a")) (re.opt (str.to.re "b")))))
(check-sat)
