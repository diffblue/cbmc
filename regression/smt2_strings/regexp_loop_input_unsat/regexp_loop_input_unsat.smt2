(declare-const bound Int)
(assert (> bound 3))
(assert (str.in.re "aaa" ((_ re.loop bound bound) (str.to.re "a"))))
(check-sat)
