; an array consisting of all #x10
(declare-const array (Array (_ BitVec 16) (_ BitVec 8)))
(assert (= array ((as const (Array (_ BitVec 16) (_ BitVec 8))) #x10)))

(declare-const index (_ BitVec 16))
(assert (not (= #x10 (select array index))))

(check-sat)
