; Indices of nested arrays are collected while iterating over the arrays.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (Array (_ BitVec 8) (_ BitVec 8))))
(declare-fun b () (Array (_ BitVec 8) (Array (_ BitVec 8) (_ BitVec 8))))
(declare-fun i () (_ BitVec 8))
(declare-fun j () (_ BitVec 8))
(assert (= (select (select a i) j) (select (select b i) j)))
(assert (not (= (select (select a i) j) (select (select b i) j))))
(check-sat)
