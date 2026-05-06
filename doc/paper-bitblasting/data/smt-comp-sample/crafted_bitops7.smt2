(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC3.

|)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun x () (_ BitVec 3))
(declare-fun y () (_ BitVec 2))
(assert (not (=> (= ((_ extract 2 2) x) (_ bv0 1)) (= ((_ extract 5 5) (bvadd (bvmul (_ bv10 6) (concat (_ bv0 3) x)) (concat (_ bv0 4) y))) (_ bv0 1)))))
(check-sat)
(exit)
