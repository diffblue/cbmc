(assert (str.in.re "a" (re.++ (re.+ (str.to.re "a")) (re.+ re.allchar))))
(check-sat)
