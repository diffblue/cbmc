; Z3#7842: multiple NaN bit patterns exist
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.isNaN x))
(assert (not (= x (_ NaN 8 24))))
(check-sat)
