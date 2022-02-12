; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)
; var_id: main::1::x; 2
; var_id: main::1::y; 1

; find_symbols
(declare-fun |tmp| () (_ BitVec 64))
(declare-fun |inv_9| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::1::val| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (= |alloc_0| ((as const (Array (_ BitVec 64) (_ BitVec 64))) (_ bv0 64))) 
    (|inv_9| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::$tmp::return_value_nondet_int$1| |main::$tmp::return_value_nondet_int$2| |main::1::val| |main::1::L| |main::1::i| |main::1::j| |alloc_0| |memor_0|))))

(declare-fun |inv_8| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1_3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$2_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$2_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$2_3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_3| (_ BitVec 32)) (|main::1::val| (_ BitVec 64)) (|main::1::val_1| (_ BitVec 64)) (|main::1::val_2| (_ BitVec 64)) (|main::1::val_3| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)) (|main::1::L_2| (_ BitVec 64)) (|main::1::L_3| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)) (|main::1::i_2| (_ BitVec 64)) (|main::1::i_3| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)) (|main::1::j_1| (_ BitVec 64)) (|main::1::j_2| (_ BitVec 64)) (|main::1::j_3| (_ BitVec 64)))
  (=> (and 
    (|inv_9| |main::$tmp::return_value_nondet_int_3| |main::$tmp::return_value_nondet_int$0_3| |main::$tmp::return_value_nondet_int$1_3| |main::$tmp::return_value_nondet_int$2_3| |main::1::val_3| |main::1::L_3| |main::1::i_3| |main::1::j_3| |alloc_0| |memor_0|)
       (= |main::$tmp::return_value_nondet_int$0_3| |main::$tmp::return_value_nondet_int$0_2|)
       (= |main::$tmp::return_value_nondet_int$1_3| |main::$tmp::return_value_nondet_int$1_2|)
       (= |main::$tmp::return_value_nondet_int$2_3| |main::$tmp::return_value_nondet_int$2_2|)
       (= |main::1::val_3| |main::1::val_2|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int_3|) |main::1::L_2|)
       (= |main::1::i_3| |main::1::i_2|)
       (= |main::1::j_3| |main::1::j_2|)
       (= |main::$tmp::return_value_nondet_int$1_2| |main::$tmp::return_value_nondet_int$1_1|)
       (= |main::$tmp::return_value_nondet_int$2_2| |main::$tmp::return_value_nondet_int$2_1|)
       (= |main::1::val_2| |main::1::val_1|)
       (= |main::1::L_2| |main::1::L_1|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$0_2|) |main::1::i_1|)
       (= |main::1::j_2| |main::1::j_1|)
       (= |main::$tmp::return_value_nondet_int$2_1| |main::$tmp::return_value_nondet_int$2|)
       (= |main::1::val_1| |main::1::val|)
       (= |main::1::L_1| |main::1::L|)
       (= |main::1::i_1| |main::1::i|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$1_1|) |main::1::j|)) 
    (|inv_8| |main::$tmp::return_value_nondet_int$2| |main::1::val| |main::1::L| |main::1::i| |main::1::j| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::1::val| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_8| |main::$tmp::return_value_nondet_int$2| |main::1::val| |main::1::L| |main::1::i| |main::1::j| |alloc_0| |memor_0|)
       (not (and (and (bvugt |main::1::L| (_ bv10 64))
       (bvult |main::1::i| |main::1::L|))
       (bvult |main::1::j| |main::1::L|)))) true)))

(declare-fun |inv_7| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::1::val| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_8| |main::$tmp::return_value_nondet_int$2| |main::1::val| |main::1::L| |main::1::i| |main::1::j| |alloc_0| |memor_0|)
       (and (and (bvugt |main::1::L| (_ bv10 64))
       (bvult |main::1::i| |main::1::L|))
       (bvult |main::1::j| |main::1::L|))) 
    (|inv_7| |main::$tmp::return_value_nondet_int$2| |main::1::val| |main::1::i| |main::1::j| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_2| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$2_1| (_ BitVec 32)) (|main::1::val| (_ BitVec 64)) (|main::1::val_1| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)) (|main::1::j_1| (_ BitVec 64)))
  (=> (and 
    (|inv_7| |main::$tmp::return_value_nondet_int$2_1| |main::1::val_1| |main::1::i_1| |main::1::j_1| |alloc_2| |memor_1|)
       (= |alloc_0| (store |alloc_1| (_ bv1 64) (select |alloc_1| (_ bv2 64))))
       (= |memor_0| (store |memor_1| (select |alloc_1| (_ bv2 64)) (store (select |memor_1| (select |alloc_1| (_ bv2 64))) |main::1::i_1| ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$2_1|))))
       (= |alloc_1| (store |alloc_2| (_ bv2 64) (_ bv2 64)))
       (= (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::i_1|) |main::1::val|)
       (= |main::1::i_1| |main::1::i|)
       (= |main::1::j_1| |main::1::j|)
       (or (= (select |alloc_0| (_ bv1 64)) (_ bv0 64)) (= (select |alloc_1| (_ bv2 64)) (_ bv0 64)))) false)))

(declare-fun |inv_5| ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_2| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$2_1| (_ BitVec 32)) (|main::1::val| (_ BitVec 64)) (|main::1::val_1| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)) (|main::1::j_1| (_ BitVec 64)))
  (=> (and 
    (|inv_7| |main::$tmp::return_value_nondet_int$2_1| |main::1::val_1| |main::1::i_1| |main::1::j_1| |alloc_2| |memor_1|)
       (= |alloc_0| (store |alloc_1| (_ bv1 64) (select |alloc_1| (_ bv2 64))))
       (= |memor_0| (store |memor_1| (select |alloc_1| (_ bv2 64)) (store (select |memor_1| (select |alloc_1| (_ bv2 64))) |main::1::i_1| ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$2_1|))))
       (= |alloc_1| (store |alloc_2| (_ bv2 64) (_ bv2 64)))
       (= (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::i_1|) |main::1::val|)
       (= |main::1::i_1| |main::1::i|)
       (= |main::1::j_1| |main::1::j|)) 
    (|inv_5| |main::1::val| |main::1::i| |main::1::j| |alloc_0| |memor_0|))))

(declare-fun |inv_3| ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::val| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_5| |main::1::val| |main::1::i| |main::1::j| |alloc_0| |memor_0|)
       (not (not (bvsge |main::1::val| (_ bv0 64))))) 
    (|inv_3| |main::1::val| |main::1::i| |main::1::j| |alloc_0| |memor_0|))))

(declare-fun |inv_4| ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::val| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_5| |main::1::val| |main::1::i| |main::1::j| |alloc_0| |memor_0|)
       (not (bvsge |main::1::val| (_ bv0 64)))) 
    (|inv_4| |main::1::val| |main::1::i| |main::1::j| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::val| (_ BitVec 64)) (|main::1::val_1| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)) (|main::1::j_1| (_ BitVec 64)))
  (=> (and 
    (|inv_4| |main::1::val_1| |main::1::i_1| |main::1::j_1| |alloc_0| |memor_0|)
       (= (bvneg |main::1::val_1|) |main::1::val|)
       (= |main::1::i_1| |main::1::i|)
       (= |main::1::j_1| |main::1::j|)) 
    (|inv_3| |main::1::val| |main::1::i| |main::1::j| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::val| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_3| |main::1::val| |main::1::i| |main::1::j| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv2 64)) (store (select |memor_1| (select |alloc_0| (_ bv2 64))) |main::1::j| |main::1::val|)))
       (= (select |alloc_0| (_ bv2 64)) (_ bv0 64))) false)))

(declare-fun |inv_2| ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::val| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_3| |main::1::val| |main::1::i| |main::1::j| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv2 64)) (store (select |memor_1| (select |alloc_0| (_ bv2 64))) |main::1::j| |main::1::val|)))) 
    (|inv_2| |main::1::i| |main::1::j| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_2| |main::1::i| |main::1::j| |alloc_0| |memor_0|)
       (not (bvsle (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::j|)))
       (= (select |alloc_0| (_ bv1 64)) (_ bv0 64))) false)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_2| |main::1::i| |main::1::j| |alloc_0| |memor_0|)
       (not (bvsle (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::j|)))) false)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_2| |main::1::i| |main::1::j| |alloc_0| |memor_0|)
       (bvsle (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::j|))
       (= (select |alloc_0| (_ bv1 64)) (_ bv0 64))) false)))

(declare-fun |inv_1| ((Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_2| |main::1::i| |main::1::j| |alloc_0| |memor_0|)
       (bvsle (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::j|))) 
    (|inv_1| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))))
  (=> 
    (|inv_1| |alloc_0| |memor_0|) true)))

(check-sat)