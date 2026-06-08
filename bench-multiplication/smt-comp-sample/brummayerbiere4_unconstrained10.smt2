(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
This benchmark demonstrates the need for propagating unconstrained bit-vectors.

Contributed by Robert Brummayer (robert.brummayer@gmail.com)
|)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun v1 () (_ BitVec 2048))
(declare-fun v3 () (_ BitVec 1024))
(declare-fun v2 () (_ BitVec 2048))
(declare-fun v4 () (_ BitVec 1024))
(declare-fun v5 () (_ BitVec 1024))
(assert (not (= (ite (not (= ((_ extract 1024 1) (bvmul v1 v2)) (bvudiv (bvudiv v4 v5) (bvudiv (bvudiv v3 v4) (bvudiv v3 v5))))) (_ bv1 1) (_ bv0 1)) (_ bv0 1))))
(check-sat)
(exit)
