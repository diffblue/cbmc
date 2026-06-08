(set-logic QF_BV)
; N2 controlled experiment benchmark.
; Pattern: commutativity, variant: E0_int_seq, bitwidth: 6
(declare-fun a () (_ BitVec 6))
(declare-fun b () (_ BitVec 6))
(define-fun prod_ab () (_ BitVec 12) (bvadd (bvadd (bvadd (bvadd (bvadd (bvand ((_ sign_extend 11) ((_ extract 0 0) b)) ((_ zero_extend 6) a)) (bvshl (bvand ((_ sign_extend 11) ((_ extract 1 1) b)) ((_ zero_extend 6) a)) (_ bv1 12))) (bvshl (bvand ((_ sign_extend 11) ((_ extract 2 2) b)) ((_ zero_extend 6) a)) (_ bv2 12))) (bvshl (bvand ((_ sign_extend 11) ((_ extract 3 3) b)) ((_ zero_extend 6) a)) (_ bv3 12))) (bvshl (bvand ((_ sign_extend 11) ((_ extract 4 4) b)) ((_ zero_extend 6) a)) (_ bv4 12))) (bvshl (bvand ((_ sign_extend 11) ((_ extract 5 5) b)) ((_ zero_extend 6) a)) (_ bv5 12))))
(define-fun prod_ba () (_ BitVec 12) (bvadd (bvadd (bvadd (bvadd (bvadd (bvand ((_ sign_extend 11) ((_ extract 0 0) a)) ((_ zero_extend 6) b)) (bvshl (bvand ((_ sign_extend 11) ((_ extract 1 1) a)) ((_ zero_extend 6) b)) (_ bv1 12))) (bvshl (bvand ((_ sign_extend 11) ((_ extract 2 2) a)) ((_ zero_extend 6) b)) (_ bv2 12))) (bvshl (bvand ((_ sign_extend 11) ((_ extract 3 3) a)) ((_ zero_extend 6) b)) (_ bv3 12))) (bvshl (bvand ((_ sign_extend 11) ((_ extract 4 4) a)) ((_ zero_extend 6) b)) (_ bv4 12))) (bvshl (bvand ((_ sign_extend 11) ((_ extract 5 5) a)) ((_ zero_extend 6) b)) (_ bv5 12))))
(assert (not (= prod_ab prod_ba)))
(check-sat)
(exit)
