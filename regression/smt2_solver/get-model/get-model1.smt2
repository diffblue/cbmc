(set-logic QF_BV)
(set-option :produce-models true)

(declare-const var_x (_ BitVec 8)) ; nullary function
(declare-const var_y (_ BitVec 8)) ; nullary function
(declare-const var_z (_ BitVec 8)) ; nullary function

(assert (= var_x #x01))
(assert (= var_y #x02))
(assert (= var_z (bvadd var_x var_y)))

(check-sat)
(get-model)
