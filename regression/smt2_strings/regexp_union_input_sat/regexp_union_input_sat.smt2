(declare-const in1 String)
(declare-const in2 String)
(assert (str.in.re "ab" (re.union (str.to.re in1) (str.to.re in2))))
(check-sat)
