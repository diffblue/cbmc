(assert (str.in.re "aaa" ((_ re.loop 1 2) (str.to.re "a"))))
(check-sat)
