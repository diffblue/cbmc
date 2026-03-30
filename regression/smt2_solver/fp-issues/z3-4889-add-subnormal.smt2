; Z3#4889: adding subnormal to large normal doesn't change it
(set-logic QF_FP)
(declare-fun c () (_ FloatingPoint 11 53))
(declare-fun d () (_ FloatingPoint 11 53))
(assert (fp.isSubnormal d))
(assert (= c (fp.add RTZ c d)))
(assert (not (fp.isZero d)))
(assert (fp.isNormal c))
(check-sat)
