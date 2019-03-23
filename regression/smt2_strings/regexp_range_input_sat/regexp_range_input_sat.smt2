(declare-const lower String)
(declare-const upper String)
(assert (str.in.re "c" (re.range lower upper)))
(check-sat)
