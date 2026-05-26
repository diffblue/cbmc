(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
    Sequential equivalence checking.
    Calypto Design Systems, Inc. <www.calypto.com>
  |)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun P_2 () (_ BitVec 32))
(declare-fun P_3 () (_ BitVec 65))
(assert (let ((?v_0 (bvmul ((_ sign_extend 65) P_2) ((_ sign_extend 32) P_3)))) (not (= (ite (not (= (bvnot ((_ extract 96 65) ?v_0)) (concat (_ bv0 31) (_ bv0 1)))) (_ bv1 1) (_ bv0 1)) (ite (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (ite (= (_ bv0 1) (_ bv0 1)) false true) (ite (= ((_ extract 65 65) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 66 66) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 67 67) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 68 68) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 69 69) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 70 70) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 71 71) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 72 72) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 73 73) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 74 74) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 75 75) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 76 76) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 77 77) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 78 78) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 79 79) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 80 80) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 81 81) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 82 82) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 83 83) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 84 84) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 85 85) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 86 86) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 87 87) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 88 88) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 89 89) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 90 90) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 91 91) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 92 92) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 93 93) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 94 94) ?v_0) (_ bv0 1)) false true)) (ite (= ((_ extract 95 95) ?v_0) (_ bv0 1)) false true))) (_ bv1 1) (_ bv0 1))))))
(check-sat)
(exit)
