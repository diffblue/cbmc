(declare-const in1 String)
(declare-const in2 String)
(assert (str.in.re "aaabbb" (re.++ (re.+ (str.to.re in1)) (re.+ (str.to.re in2)))))
(check-sat)
