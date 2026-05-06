(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
    Sequential equivalence checking.
    Calypto Design Systems, Inc. <www.calypto.com>
  |)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun P_2 () (_ BitVec 1024))
(assert (let ((?v_1 ((_ extract 209 192) P_2)) (?v_0 ((_ extract 401 384) P_2))) (let ((?v_2 (bvmul ?v_0 ((_ extract 17 0) P_2))) (?v_3 ((_ extract 337 320) P_2))) (not (= (bvadd (bvsub (concat ((_ extract 336 320) P_2) (_ bv0 1)) ?v_1) (bvadd ?v_0 ?v_2)) (bvadd (bvadd (bvsub (bvadd ?v_3 ?v_0) ?v_1) ?v_2) ?v_3))))))
(check-sat)
(exit)
