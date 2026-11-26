; get-model must print quoted symbols in |...| form
(set-logic QF_BV)
(declare-const |a b| (_ BitVec 8))
(assert (= |a b| #x81))
(check-sat)
(get-model)
