(assert (str.in.re "aaa" (re.++ (re.+ (str.to.re "a")) (re.opt (str.to.re "b")))))
(check-sat)
