; Z3#6457: isNaN of (inf - (a + b)) — only NaN if a+b is also inf
(set-logic QF_FP)
(declare-const a (_ FloatingPoint 8 24))
(declare-const b (_ FloatingPoint 8 24))
(assert (fp.isNaN (fp.sub RNE (_ +oo 8 24) (fp.add RNE a b))))
(check-sat)
