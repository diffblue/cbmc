; CVC5#11139: fp.div RTN of fp.fma RTP result on Float64.
(set-logic QF_FP)
(declare-const a (_ FloatingPoint 11 53))
(declare-const b (_ FloatingPoint 11 53))
(assert (= (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)
  (fp.div RTN (fp.fma RTP a a
    (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)) b)))
(check-sat)
