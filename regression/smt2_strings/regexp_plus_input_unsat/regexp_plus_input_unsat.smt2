(declare-const in String)
(assert (str.in.re "aabb" (re.++ (re.+ (str.to.re in)) (re.+ (str.to.re in)))))
(check-sat)
