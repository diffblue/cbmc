; Z3#6117: fp.fma RTP with specific Float64 values.
(set-logic QF_FP)
(declare-const a (_ FloatingPoint 11 53))
(declare-const b (_ FloatingPoint 11 53))
(assert (= a (fp #b1 #b11111111110 #b1111111111111111111111111111111111111111111111111111)))
(assert (= b (fp #b0 #b11111110111 #b1111101100111000010100011011001111010101111001101010)))
(assert (= (fp.fma RTP b a a) a))
(check-sat)
