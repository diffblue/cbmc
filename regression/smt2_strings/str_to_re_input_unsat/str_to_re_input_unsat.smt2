(declare-const in String)
(assert (str.in.re "abba" (re.+ (str.to.re in))))
(assert (str.in.re "cddc" (re.+ (str.to.re in))))
(check-sat)
