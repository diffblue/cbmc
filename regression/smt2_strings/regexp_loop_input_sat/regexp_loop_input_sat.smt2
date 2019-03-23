(declare-const lower Int)
(declare-const upper Int)
(assert (str.in.re "aaa" ((_ re.loop lower upper) (str.to.re "a"))))
(check-sat)
