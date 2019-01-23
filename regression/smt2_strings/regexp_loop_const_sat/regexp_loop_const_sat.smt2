(assert (str.in.re "aaa" ((_ re.loop 3 3) (str.to.re "a"))))
(check-sat)
