(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC3.

|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
(declare-fun a () (_ BitVec 32))
(assert (= a (_ bv0 32)))
(assert (= c ((_ extract 7 0) (bvlshr (bvmul (bvand (bvmul (concat a b) (_ bv2149582850 40)) (_ bv36578664720 40)) (_ bv4311810305 40)) (_ bv32 40)))))
(assert (not (= b (concat (concat (concat (concat (concat (concat (concat ((_ extract 0 0) c) ((_ extract 1 1) c)) ((_ extract 2 2) c)) ((_ extract 3 3) c)) ((_ extract 4 4) c)) ((_ extract 5 5) c)) ((_ extract 6 6) c)) ((_ extract 7 7) c)))))
(check-sat)
(exit)
