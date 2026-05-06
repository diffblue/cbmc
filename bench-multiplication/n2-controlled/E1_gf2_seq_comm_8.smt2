(set-logic QF_BV)
; N2 controlled experiment benchmark.
; Pattern: commutativity, variant: E1_gf2_seq, bitwidth: 8
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(define-fun prod_ab () (_ BitVec 16) (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvand ((_ sign_extend 15) ((_ extract 0 0) b)) ((_ zero_extend 8) a)) (bvshl (bvand ((_ sign_extend 15) ((_ extract 1 1) b)) ((_ zero_extend 8) a)) (_ bv1 16))) (bvshl (bvand ((_ sign_extend 15) ((_ extract 2 2) b)) ((_ zero_extend 8) a)) (_ bv2 16))) (bvshl (bvand ((_ sign_extend 15) ((_ extract 3 3) b)) ((_ zero_extend 8) a)) (_ bv3 16))) (bvshl (bvand ((_ sign_extend 15) ((_ extract 4 4) b)) ((_ zero_extend 8) a)) (_ bv4 16))) (bvshl (bvand ((_ sign_extend 15) ((_ extract 5 5) b)) ((_ zero_extend 8) a)) (_ bv5 16))) (bvshl (bvand ((_ sign_extend 15) ((_ extract 6 6) b)) ((_ zero_extend 8) a)) (_ bv6 16))) (bvshl (bvand ((_ sign_extend 15) ((_ extract 7 7) b)) ((_ zero_extend 8) a)) (_ bv7 16))))
(define-fun prod_ba () (_ BitVec 16) (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvand ((_ sign_extend 15) ((_ extract 0 0) a)) ((_ zero_extend 8) b)) (bvshl (bvand ((_ sign_extend 15) ((_ extract 1 1) a)) ((_ zero_extend 8) b)) (_ bv1 16))) (bvshl (bvand ((_ sign_extend 15) ((_ extract 2 2) a)) ((_ zero_extend 8) b)) (_ bv2 16))) (bvshl (bvand ((_ sign_extend 15) ((_ extract 3 3) a)) ((_ zero_extend 8) b)) (_ bv3 16))) (bvshl (bvand ((_ sign_extend 15) ((_ extract 4 4) a)) ((_ zero_extend 8) b)) (_ bv4 16))) (bvshl (bvand ((_ sign_extend 15) ((_ extract 5 5) a)) ((_ zero_extend 8) b)) (_ bv5 16))) (bvshl (bvand ((_ sign_extend 15) ((_ extract 6 6) a)) ((_ zero_extend 8) b)) (_ bv6 16))) (bvshl (bvand ((_ sign_extend 15) ((_ extract 7 7) a)) ((_ zero_extend 8) b)) (_ bv7 16))))
(assert (not (= prod_ab prod_ba)))
(check-sat)
(exit)
