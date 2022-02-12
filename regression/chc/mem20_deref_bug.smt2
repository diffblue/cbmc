; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)
; var_id: main::1::x; 1
; var_id: main::1::y; 2

; find_symbols
(declare-fun |tmp| () (_ BitVec 64))
(declare-fun |inv_12| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (= |alloc_0| ((as const (Array (_ BitVec 64) (_ BitVec 64))) (_ bv0 64))) 
    (|inv_12| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(declare-fun |inv_11| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_1| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_12| |main::$tmp::return_value_nondet_int_1| |main::$tmp::return_value_nondet_int$0_1| |main::1::1::i_1| |main::1::L_1| |alloc_0| |memor_0|)
       (= |main::$tmp::return_value_nondet_int$0_1| |main::$tmp::return_value_nondet_int$0|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int_1|) |main::1::L|)) 
    (|inv_11| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_11| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|)
       (not (bvugt |main::1::L| (_ bv0 64)))) true)))

(declare-fun |inv_10| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_11| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|)
       (bvugt |main::1::L| (_ bv0 64))) 
    (|inv_10| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(declare-fun |inv_3| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_1| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_10| |main::$tmp::return_value_nondet_int$0_1| |main::1::1::i_1| |main::1::L_1| |alloc_1| |memor_0|)
       (= |alloc_0| (store |alloc_1| (_ bv1 64) (_ bv1 64)))
       (= |main::$tmp::return_value_nondet_int$0_1| |main::$tmp::return_value_nondet_int$0|)
       (= (_ bv0 64) |main::1::1::i|)
       (= |main::1::L_1| |main::1::L|)) 
    (|inv_3| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(declare-fun |inv_7| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_3| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|)
       (not (bvuge |main::1::1::i| |main::1::L|))) 
    (|inv_7| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(declare-fun |inv_8| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_7| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|)
       (not (not (= |main::$tmp::return_value_nondet_int$0| (_ bv0 32))))) 
    (|inv_8| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_8| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv2 64)) (store (select |memor_1| (select |alloc_0| (_ bv2 64))) |main::1::1::i| |main::1::1::i|)))
       (= (select |alloc_0| (_ bv2 64)) (_ bv0 64))) false)))

(declare-fun |inv_5| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_8| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv2 64)) (store (select |memor_1| (select |alloc_0| (_ bv2 64))) |main::1::1::i| |main::1::1::i|)))) 
    (|inv_5| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(declare-fun |inv_6| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_7| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|)
       (not (= |main::$tmp::return_value_nondet_int$0| (_ bv0 32)))) 
    (|inv_6| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_6| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv1 64)) (store (select |memor_1| (select |alloc_0| (_ bv1 64))) |main::1::1::i| |main::1::1::i|)))
       (= (select |alloc_0| (_ bv1 64)) (_ bv0 64))) false)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_6| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv1 64)) (store (select |memor_1| (select |alloc_0| (_ bv1 64))) |main::1::1::i| |main::1::1::i|)))) 
    (|inv_5| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_1| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_5| |main::$tmp::return_value_nondet_int$0_1| |main::1::1::i_1| |main::1::L_1| |alloc_0| |memor_0|)
       (= |main::$tmp::return_value_nondet_int$0_1| |main::$tmp::return_value_nondet_int$0|)
       (= (bvadd |main::1::1::i_1| (_ bv1 64)) |main::1::1::i|)
       (= |main::1::L_1| |main::1::L|)) 
    (|inv_3| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(declare-fun |inv_1| ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> 
    (|inv_3| |main::$tmp::return_value_nondet_int$0| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|) 
    (|inv_1| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::1::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_1| |main::1::1::i| |main::1::L| |alloc_0| |memor_0|)
       (not (not (bvuge |main::1::1::i| |main::1::L|)))) true)))

(check-sat)