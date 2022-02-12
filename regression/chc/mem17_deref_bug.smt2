; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)
; var_id: main::1::x; 2
; var_id: main::1::y; 1

; find_symbols
(declare-fun |tmp| () (_ BitVec 64))
(declare-fun |inv_16| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (= |alloc_0| ((as const (Array (_ BitVec 64) (_ BitVec 64))) (_ bv0 64))) 
    (|inv_16| |main::$tmp::return_value_nondet_int| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(declare-fun |inv_4| ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int_2| (_ BitVec 32)) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0_1| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0_2| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_1| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_2| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t1_1| (_ BitVec 64)) (|main::1::1::1::t1_2| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::1::t2_1| (_ BitVec 64)) (|main::1::1::1::t2_2| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::1::i_2| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)) (|main::1::L_2| (_ BitVec 64)))
  (=> (and 
    (|inv_16| |main::$tmp::return_value_nondet_int_2| |main::$tmp::tmp_if_expr_2| |main::$tmp::tmp_if_expr$0_2| |main::1::1::1::t1_2| |main::1::1::1::t2_2| |main::1::1::i_2| |main::1::L_2| |alloc_1| |memor_0|)
       (= |alloc_0| (store |alloc_1| (_ bv1 64) (_ bv1 64)))
       (= |main::$tmp::tmp_if_expr_2| |main::$tmp::tmp_if_expr_1|)
       (= |main::$tmp::tmp_if_expr$0_2| |main::$tmp::tmp_if_expr$0_1|)
       (= |main::1::1::1::t1_2| |main::1::1::1::t1_1|)
       (= |main::1::1::1::t2_2| |main::1::1::1::t2_1|)
       (= |main::1::1::i_2| |main::1::1::i_1|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int_2|) |main::1::L_1|)
       (= |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr|)
       (= |main::$tmp::tmp_if_expr$0_1| |main::$tmp::tmp_if_expr$0|)
       (= |main::1::1::1::t1_1| |main::1::1::1::t1|)
       (= |main::1::1::1::t2_1| |main::1::1::1::t2|)
       (= (_ bv0 64) |main::1::1::i|)
       (= |main::1::L_1| |main::1::L|)) 
    (|inv_4| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(declare-fun |inv_13| ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_4| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|)
       (not (bvuge |main::1::1::i| |main::1::L|))) 
    (|inv_13| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_13| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|)
       (not (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv2 64))) |main::1::1::i|))))
       (or (= (select |alloc_0| (_ bv1 64)) (_ bv0 64)) (= (select |alloc_0| (_ bv2 64)) (_ bv0 64)))) false)))

(declare-fun |inv_14| ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_13| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|)
       (not (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv2 64))) |main::1::1::i|))))) 
    (|inv_14| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0_1| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_1| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t1_1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::1::t2_1| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_14| |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr$0_1| |main::1::1::1::t1_1| |main::1::1::1::t2_1| |main::1::1::i_1| |main::1::L_1| |alloc_0| |memor_0|)
       (= (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::1::i_1|) |main::$tmp::tmp_if_expr|)
       (= |main::$tmp::tmp_if_expr$0_1| |main::$tmp::tmp_if_expr$0|)
       (= |main::1::1::1::t1_1| |main::1::1::1::t1|)
       (= |main::1::1::1::t2_1| |main::1::1::1::t2|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= |main::1::L_1| |main::1::L|)
       (= (select |alloc_0| (_ bv1 64)) (_ bv0 64))) false)))

(declare-fun |inv_11| ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0_1| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_1| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t1_1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::1::t2_1| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_14| |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr$0_1| |main::1::1::1::t1_1| |main::1::1::1::t2_1| |main::1::1::i_1| |main::1::L_1| |alloc_0| |memor_0|)
       (= (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::1::i_1|) |main::$tmp::tmp_if_expr|)
       (= |main::$tmp::tmp_if_expr$0_1| |main::$tmp::tmp_if_expr$0|)
       (= |main::1::1::1::t1_1| |main::1::1::1::t1|)
       (= |main::1::1::1::t2_1| |main::1::1::1::t2|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= |main::1::L_1| |main::1::L|)) 
    (|inv_11| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_13| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|)
       (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv2 64))) |main::1::1::i|)))
       (or (= (select |alloc_0| (_ bv1 64)) (_ bv0 64)) (= (select |alloc_0| (_ bv2 64)) (_ bv0 64)))) false)))

(declare-fun |inv_12| ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_13| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|)
       (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv2 64))) |main::1::1::i|)))) 
    (|inv_12| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0_1| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_1| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t1_1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::1::t2_1| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_12| |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr$0_1| |main::1::1::1::t1_1| |main::1::1::1::t2_1| |main::1::1::i_1| |main::1::L_1| |alloc_0| |memor_0|)
       (= (select (select |memor_0| (select |alloc_0| (_ bv2 64))) |main::1::1::i_1|) |main::$tmp::tmp_if_expr|)
       (= |main::$tmp::tmp_if_expr$0_1| |main::$tmp::tmp_if_expr$0|)
       (= |main::1::1::1::t1_1| |main::1::1::1::t1|)
       (= |main::1::1::1::t2_1| |main::1::1::1::t2|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= |main::1::L_1| |main::1::L|)
       (= (select |alloc_0| (_ bv2 64)) (_ bv0 64))) false)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0_1| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_1| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t1_1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::1::t2_1| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_12| |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr$0_1| |main::1::1::1::t1_1| |main::1::1::1::t2_1| |main::1::1::i_1| |main::1::L_1| |alloc_0| |memor_0|)
       (= (select (select |memor_0| (select |alloc_0| (_ bv2 64))) |main::1::1::i_1|) |main::$tmp::tmp_if_expr|)
       (= |main::$tmp::tmp_if_expr$0_1| |main::$tmp::tmp_if_expr$0|)
       (= |main::1::1::1::t1_1| |main::1::1::1::t1|)
       (= |main::1::1::1::t2_1| |main::1::1::1::t2|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= |main::1::L_1| |main::1::L|)) 
    (|inv_11| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(declare-fun |inv_9| ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0_1| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_1| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t1_1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::1::t2_1| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_11| |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr$0_1| |main::1::1::1::t1_1| |main::1::1::1::t2_1| |main::1::1::i_1| |main::1::L_1| |alloc_0| |memor_0|)
       (= |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr|)
       (= |main::$tmp::tmp_if_expr$0_1| |main::$tmp::tmp_if_expr$0|)
       (= |main::$tmp::tmp_if_expr_1| |main::1::1::1::t1|)
       (= |main::1::1::1::t2_1| |main::1::1::1::t2|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= |main::1::L_1| |main::1::L|)) 
    (|inv_9| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_9| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|)
       (not (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv2 64))) |main::1::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::1::i|))))
       (or (= (select |alloc_0| (_ bv1 64)) (_ bv0 64)) (= (select |alloc_0| (_ bv2 64)) (_ bv0 64)))) false)))

(declare-fun |inv_10| ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_9| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|)
       (not (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv2 64))) |main::1::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::1::i|))))) 
    (|inv_10| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0_1| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_1| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t1_1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::1::t2_1| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_10| |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr$0_1| |main::1::1::1::t1_1| |main::1::1::1::t2_1| |main::1::1::i_1| |main::1::L_1| |alloc_0| |memor_0|)
       (= |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr|)
       (= (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::1::i_1|) |main::$tmp::tmp_if_expr$0|)
       (= |main::1::1::1::t1_1| |main::1::1::1::t1|)
       (= |main::1::1::1::t2_1| |main::1::1::1::t2|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= |main::1::L_1| |main::1::L|)
       (= (select |alloc_0| (_ bv1 64)) (_ bv0 64))) false)))

(declare-fun |inv_7| ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0_1| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_1| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t1_1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::1::t2_1| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_10| |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr$0_1| |main::1::1::1::t1_1| |main::1::1::1::t2_1| |main::1::1::i_1| |main::1::L_1| |alloc_0| |memor_0|)
       (= |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr|)
       (= (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::1::i_1|) |main::$tmp::tmp_if_expr$0|)
       (= |main::1::1::1::t1_1| |main::1::1::1::t1|)
       (= |main::1::1::1::t2_1| |main::1::1::1::t2|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= |main::1::L_1| |main::1::L|)) 
    (|inv_7| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_9| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|)
       (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv2 64))) |main::1::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::1::i|)))
       (or (= (select |alloc_0| (_ bv1 64)) (_ bv0 64)) (= (select |alloc_0| (_ bv2 64)) (_ bv0 64)))) false)))

(declare-fun |inv_8| ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_9| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|)
       (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv2 64))) |main::1::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::1::i|)))) 
    (|inv_8| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0_1| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_1| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t1_1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::1::t2_1| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_8| |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr$0_1| |main::1::1::1::t1_1| |main::1::1::1::t2_1| |main::1::1::i_1| |main::1::L_1| |alloc_0| |memor_0|)
       (= |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr|)
       (= (select (select |memor_0| (select |alloc_0| (_ bv2 64))) |main::1::1::i_1|) |main::$tmp::tmp_if_expr$0|)
       (= |main::1::1::1::t1_1| |main::1::1::1::t1|)
       (= |main::1::1::1::t2_1| |main::1::1::1::t2|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= |main::1::L_1| |main::1::L|)
       (= (select |alloc_0| (_ bv2 64)) (_ bv0 64))) false)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0_1| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_1| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t1_1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::1::t2_1| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_8| |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr$0_1| |main::1::1::1::t1_1| |main::1::1::1::t2_1| |main::1::1::i_1| |main::1::L_1| |alloc_0| |memor_0|)
       (= |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr|)
       (= (select (select |memor_0| (select |alloc_0| (_ bv2 64))) |main::1::1::i_1|) |main::$tmp::tmp_if_expr$0|)
       (= |main::1::1::1::t1_1| |main::1::1::1::t1|)
       (= |main::1::1::1::t2_1| |main::1::1::1::t2|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= |main::1::L_1| |main::1::L|)) 
    (|inv_7| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_2| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0_1| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0_2| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_1| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_2| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t1_1| (_ BitVec 64)) (|main::1::1::1::t1_2| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::1::t2_1| (_ BitVec 64)) (|main::1::1::1::t2_2| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::1::i_2| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)) (|main::1::L_2| (_ BitVec 64)))
  (=> (and 
    (|inv_7| |main::$tmp::tmp_if_expr_2| |main::$tmp::tmp_if_expr$0_2| |main::1::1::1::t1_2| |main::1::1::1::t2_2| |main::1::1::i_2| |main::1::L_2| |alloc_0| |memor_2|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv1 64)) (store (select |memor_1| (select |alloc_0| (_ bv1 64))) |main::1::1::i_1| |main::1::1::1::t2_1|)))
       (= |memor_1| (store |memor_2| (select |alloc_0| (_ bv2 64)) (store (select |memor_2| (select |alloc_0| (_ bv2 64))) |main::1::1::i_1| |main::1::1::1::t1_1|)))
       (= |main::$tmp::tmp_if_expr_2| |main::$tmp::tmp_if_expr_1|)
       (= |main::$tmp::tmp_if_expr$0_2| |main::$tmp::tmp_if_expr$0_1|)
       (= |main::1::1::1::t1_2| |main::1::1::1::t1_1|)
       (= |main::$tmp::tmp_if_expr$0_2| |main::1::1::1::t2_1|)
       (= |main::1::1::i_2| |main::1::1::i_1|)
       (= |main::1::L_2| |main::1::L_1|)
       (= |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr|)
       (= |main::$tmp::tmp_if_expr$0_1| |main::$tmp::tmp_if_expr$0|)
       (= |main::1::1::1::t1_1| |main::1::1::1::t1|)
       (= |main::1::1::1::t2_1| |main::1::1::1::t2|)
       (= (bvadd |main::1::1::i_1| (_ bv1 64)) |main::1::1::i|)
       (= |main::1::L_1| |main::1::L|)
       (or (= (select |alloc_0| (_ bv1 64)) (_ bv0 64)) (= (select |alloc_0| (_ bv2 64)) (_ bv0 64)))) false)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_2| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0_1| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0_2| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_1| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_2| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t1_1| (_ BitVec 64)) (|main::1::1::1::t1_2| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::1::t2_1| (_ BitVec 64)) (|main::1::1::1::t2_2| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::1::i_2| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)) (|main::1::L_2| (_ BitVec 64)))
  (=> (and 
    (|inv_7| |main::$tmp::tmp_if_expr_2| |main::$tmp::tmp_if_expr$0_2| |main::1::1::1::t1_2| |main::1::1::1::t2_2| |main::1::1::i_2| |main::1::L_2| |alloc_0| |memor_2|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv1 64)) (store (select |memor_1| (select |alloc_0| (_ bv1 64))) |main::1::1::i_1| |main::1::1::1::t2_1|)))
       (= |memor_1| (store |memor_2| (select |alloc_0| (_ bv2 64)) (store (select |memor_2| (select |alloc_0| (_ bv2 64))) |main::1::1::i_1| |main::1::1::1::t1_1|)))
       (= |main::$tmp::tmp_if_expr_2| |main::$tmp::tmp_if_expr_1|)
       (= |main::$tmp::tmp_if_expr$0_2| |main::$tmp::tmp_if_expr$0_1|)
       (= |main::1::1::1::t1_2| |main::1::1::1::t1_1|)
       (= |main::$tmp::tmp_if_expr$0_2| |main::1::1::1::t2_1|)
       (= |main::1::1::i_2| |main::1::1::i_1|)
       (= |main::1::L_2| |main::1::L_1|)
       (= |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr|)
       (= |main::$tmp::tmp_if_expr$0_1| |main::$tmp::tmp_if_expr$0|)
       (= |main::1::1::1::t1_1| |main::1::1::1::t1|)
       (= |main::1::1::1::t2_1| |main::1::1::1::t2|)
       (= (bvadd |main::1::1::i_1| (_ bv1 64)) |main::1::1::i|)
       (= |main::1::L_1| |main::1::L|)) 
    (|inv_4| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(declare-fun |inv_1| ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr$0| (_ BitVec 64)) (|main::1::1::1::t1| (_ BitVec 64)) (|main::1::1::1::t2| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> 
    (|inv_4| |main::$tmp::tmp_if_expr| |main::$tmp::tmp_if_expr$0| |main::1::1::1::t1| |main::1::1::1::t2| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|) 
    (|inv_1| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_1| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|)
       (not (not (bvuge |main::1::1::i| |main::1::L|)))) true)))

(check-sat)