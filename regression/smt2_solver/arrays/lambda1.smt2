(define-const array2 (Array (_ BitVec 16) (_ BitVec 16)) (lambda ((i (_ BitVec 16))) i))
(declare-const some_sample (_ BitVec 16))
(assert (= some_sample (select array2 #x1234)))

(check-sat)
(get-value (some_sample))
