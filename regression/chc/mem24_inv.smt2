; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)
; var_id: main::1::w; 4
; var_id: main::1::y; 2
; var_id: main::1::x; 1
; var_id: main::1::z; 3

(declare-fun |inv_23| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

; find_symbols
(declare-fun |tmp| () (_ BitVec 64))
(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::1::1::1::m| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> true 
    (|inv_23| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_11| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_2| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_2| (_ BitVec 32)) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_1| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_2| (_ BitVec 64)) (|main::1::1::1::m| (_ BitVec 64)) (|main::1::1::1::m_1| (_ BitVec 64)) (|main::1::1::1::m_2| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::1::i_2| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)) (|main::1::L_2| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)) (|main::1::i_2| (_ BitVec 64)))
  (=> (and 
    (|inv_23| |main::$tmp::return_value_nondet_int_2| |main::$tmp::return_value_nondet_int$0_2| |main::$tmp::tmp_if_expr_2| |main::1::1::1::m_2| |main::1::1::i_2| |main::1::L_2| |main::1::i_2| |alloc_2| |memor_0|)
       (= |alloc_0| (store |alloc_1| (_ bv2 64) (_ bv2 64)))
       (= |alloc_1| (store |alloc_2| (_ bv1 64) (_ bv1 64)))
       (= |main::$tmp::return_value_nondet_int$0_2| |main::$tmp::return_value_nondet_int$0_1|)
       (= |main::$tmp::tmp_if_expr_2| |main::$tmp::tmp_if_expr_1|)
       (= |main::1::1::1::m_2| |main::1::1::1::m_1|)
       (= |main::1::1::i_2| |main::1::1::i_1|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int_2|) |main::1::L_1|)
       (= |main::1::i_2| |main::1::i_1|)
       (= |main::$tmp::return_value_nondet_int$0_1| |main::$tmp::return_value_nondet_int$0|)
       (= |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr|)
       (= |main::1::1::1::m_1| |main::1::1::1::m|)
       (= (_ bv0 64) |main::1::1::i|)
       (= |main::1::L_1| |main::1::L|)
       (= |main::1::i_1| |main::1::i|)) 
    (|inv_11| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_20| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::1::1::1::m| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_11| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|)
       (not (bvuge |main::1::1::i| |main::1::L|))) 
    (|inv_20| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_21| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::1::1::1::m| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_20| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|)
       (not (= (bvurem |main::1::1::i| (_ bv2 64)) (_ bv0 64)))) 
    (|inv_21| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_18| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_2| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::1::1::1::m| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_21| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_2| |memor_0|)
       (= |alloc_0| (store |alloc_1| (_ bv4 64) (select |alloc_1| (_ bv1 64))))
       (= |alloc_1| (store |alloc_2| (_ bv3 64) (select |alloc_2| (_ bv2 64))))) 
    (|inv_18| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_19| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::1::1::1::m| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_20| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|)
       (= (bvurem |main::1::1::i| (_ bv2 64)) (_ bv0 64))) 
    (|inv_19| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_2| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::1::1::1::m| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_19| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_2| |memor_0|)
       (= |alloc_0| (store |alloc_1| (_ bv4 64) (select |alloc_1| (_ bv2 64))))
       (= |alloc_1| (store |alloc_2| (_ bv3 64) (select |alloc_2| (_ bv1 64))))) 
    (|inv_18| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_16| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::1::1::1::m| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> 
    (|inv_18| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|) 
    (|inv_16| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_17| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::1::1::1::m| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_16| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|)
       (not (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv4 64))) |main::1::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv3 64))) |main::1::1::i|))))) 
    (|inv_17| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_14| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_1| (_ BitVec 32)) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_1| (_ BitVec 64)) (|main::1::1::1::m| (_ BitVec 64)) (|main::1::1::1::m_1| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)))
  (=> (and 
    (|inv_17| |main::$tmp::return_value_nondet_int$0_1| |main::$tmp::tmp_if_expr_1| |main::1::1::1::m_1| |main::1::1::i_1| |main::1::L_1| |main::1::i_1| |alloc_0| |memor_0|)
       (= |main::$tmp::return_value_nondet_int$0_1| |main::$tmp::return_value_nondet_int$0|)
       (= (select (select |memor_0| (select |alloc_0| (_ bv4 64))) |main::1::1::i_1|) |main::$tmp::tmp_if_expr|)
       (= |main::1::1::1::m_1| |main::1::1::1::m|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= |main::1::L_1| |main::1::L|)
       (= |main::1::i_1| |main::1::i|)) 
    (|inv_14| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_15| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::1::1::1::m| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_16| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|)
       (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv4 64))) |main::1::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv3 64))) |main::1::1::i|)))) 
    (|inv_15| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_1| (_ BitVec 32)) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_1| (_ BitVec 64)) (|main::1::1::1::m| (_ BitVec 64)) (|main::1::1::1::m_1| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)))
  (=> (and 
    (|inv_15| |main::$tmp::return_value_nondet_int$0_1| |main::$tmp::tmp_if_expr_1| |main::1::1::1::m_1| |main::1::1::i_1| |main::1::L_1| |main::1::i_1| |alloc_0| |memor_0|)
       (= |main::$tmp::return_value_nondet_int$0_1| |main::$tmp::return_value_nondet_int$0|)
       (= (select (select |memor_0| (select |alloc_0| (_ bv3 64))) |main::1::1::i_1|) |main::$tmp::tmp_if_expr|)
       (= |main::1::1::1::m_1| |main::1::1::1::m|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= |main::1::L_1| |main::1::L|)
       (= |main::1::i_1| |main::1::i|)) 
    (|inv_14| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_2| (_ BitVec 32)) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_1| (_ BitVec 64)) (|main::$tmp::tmp_if_expr_2| (_ BitVec 64)) (|main::1::1::1::m| (_ BitVec 64)) (|main::1::1::1::m_1| (_ BitVec 64)) (|main::1::1::1::m_2| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::1::i_2| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)) (|main::1::L_2| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)) (|main::1::i_2| (_ BitVec 64)))
  (=> (and 
    (|inv_14| |main::$tmp::return_value_nondet_int$0_2| |main::$tmp::tmp_if_expr_2| |main::1::1::1::m_2| |main::1::1::i_2| |main::1::L_2| |main::1::i_2| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv1 64)) (store (select |memor_1| (select |alloc_0| (_ bv1 64))) |main::1::1::i_1| |main::1::1::1::m_1|)))
       (= |main::$tmp::return_value_nondet_int$0_2| |main::$tmp::return_value_nondet_int$0_1|)
       (= |main::$tmp::tmp_if_expr_2| |main::$tmp::tmp_if_expr_1|)
       (= |main::$tmp::tmp_if_expr_2| |main::1::1::1::m_1|)
       (= |main::1::1::i_2| |main::1::1::i_1|)
       (= |main::1::L_2| |main::1::L_1|)
       (= |main::1::i_2| |main::1::i_1|)
       (= |main::$tmp::return_value_nondet_int$0_1| |main::$tmp::return_value_nondet_int$0|)
       (= |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr|)
       (= |main::1::1::1::m_1| |main::1::1::1::m|)
       (= (bvadd |main::1::1::i_1| (_ bv1 64)) |main::1::1::i|)
       (= |main::1::L_1| |main::1::L|)
       (= |main::1::i_1| |main::1::i|)) 
    (|inv_11| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_8| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::tmp_if_expr| (_ BitVec 64)) (|main::1::1::1::m| (_ BitVec 64)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> 
    (|inv_11| |main::$tmp::return_value_nondet_int$0| |main::$tmp::tmp_if_expr| |main::1::1::1::m| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|) 
    (|inv_8| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_7| ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0_1| (_ BitVec 32)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)))
  (=> (and 
    (|inv_8| |main::$tmp::return_value_nondet_int$0_1| |main::1::1::i_1| |main::1::L_1| |main::1::i_1| |alloc_0| |memor_0|)
       (not (not (bvuge |main::1::1::i_1| |main::1::L_1|)))
       (= |main::1::L_1| |main::1::L|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$0_1|) |main::1::i|)) 
    (|inv_7| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_5| ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> 
    (|inv_7| |main::1::L| |main::1::i| |alloc_0| |memor_0|) 
    (|inv_5| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_6| ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_7| |main::1::L| |main::1::i| |alloc_0| |memor_0|)
       (not (not (bvuge |main::1::i| |main::1::L|)))) 
    (|inv_6| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_1| ((Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> 
    (|inv_6| |main::1::L| |main::1::i| |alloc_0| |memor_0|) 
    (|inv_1| |alloc_0| |memor_0|))))

(declare-fun |inv_3| ((_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_5| |main::1::L| |main::1::i| |alloc_0| |memor_0|)
       (not (bvuge |main::1::i| |main::1::L|))) 
    (|inv_3| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_3| |main::1::i| |alloc_0| |memor_0|)
       (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv2 64))) |main::1::i|)))) false)))

(declare-fun |inv_2| ((Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_3| |main::1::i| |alloc_0| |memor_0|)
       (bvsge (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv2 64))) |main::1::i|))) 
    (|inv_2| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))))
  (=> 
    (|inv_2| |alloc_0| |memor_0|) 
    (|inv_1| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))))
  (=> 
    (|inv_1| |alloc_0| |memor_0|) true)))

(check-sat)