; push/pop are not supported; must report unsupported
(set-logic QF_BV)
(push 1)
(assert false)
(pop 1)
(check-sat)
