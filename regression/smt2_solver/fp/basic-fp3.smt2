(set-logic FP)

(declare-fun a () Float16)
(declare-fun b () Float32)
(declare-fun c () Float64)
(declare-fun d () Float128)

(check-sat)
(get-model)
