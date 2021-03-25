; an array consisting of all #x10
(declare-const array (Array (_ BitVec 16) (_ BitVec 8)))
(assert (= array ((as const (Array (_ BitVec 16) (_ BitVec 8))) #x10)))

(declare-const sample (_ BitVec 8))
(assert (= sample (select array #x0000)))

(check-sat)
(get-value (sample))
