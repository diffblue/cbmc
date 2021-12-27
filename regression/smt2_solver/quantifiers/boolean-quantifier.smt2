(assert (exists ((b Bool)) b))
(assert (exists ((b Bool)) (not b)))

(assert (not (forall ((b Bool)) b)))
(assert (not (forall ((b Bool)) (not b))))

(assert (exists ((a Bool) (b Bool)) (= a b)))
(assert (not (forall ((a Bool) (b Bool)) (= a b))))

(assert (forall ((a Bool)) (exists ((b Bool)) (= a b))))

(check-sat)
(get-model)
