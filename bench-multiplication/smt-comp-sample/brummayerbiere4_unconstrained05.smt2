(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
This benchmark demonstrates the need for propagating unconstrained bit-vectors.

Contributed by Robert Brummayer (robert.brummayer@gmail.com)
|)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun v1 () (_ BitVec 1024))
(declare-fun v3 () (_ BitVec 1024))
(declare-fun v2 () (_ BitVec 1024))
(declare-fun v5 () (_ BitVec 1024))
(declare-fun v4 () (_ BitVec 1024))
(declare-fun v6 () (_ BitVec 1024))
(assert (not (= (ite (not (= (bvmul (bvudiv (bvudiv v4 v3) (bvmul v2 v5)) (bvmul (bvudiv (bvudiv v1 v2) (bvudiv v1 v3)) (bvmul (bvudiv v2 v3) (bvmul v4 v5)))) v6)) (_ bv1 1) (_ bv0 1)) (_ bv0 1))))
(check-sat)
(exit)
