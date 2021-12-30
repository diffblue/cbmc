; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)

(declare-fun |inv_15| (Bool (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

; find_symbols
(declare-fun |tmp| () (_ BitVec 64))
(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool) (|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> true 
    (|inv_15| |main::$tmp::tmp_if_expr| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::$tmp::return_value_nondet_int$1| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_14| (Bool (_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool) (|main::$tmp::tmp_if_expr_1| Bool) (|main::$tmp::tmp_if_expr_2| Bool) (|main::$tmp::return_value_nondet_int$0_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_2| (_ BitVec 32)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)) (|main::1::L_2| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)) (|main::1::i_2| (_ BitVec 64)))
  (=> (and 
    (|inv_15| |main::$tmp::tmp_if_expr_2| |main::$tmp::return_value_nondet_int_2| |main::$tmp::return_value_nondet_int$0_2| |main::$tmp::return_value_nondet_int$1_2| |main::1::L_2| |main::1::i_2| |alloc_0| |memor_0|)
       (= |main::$tmp::tmp_if_expr_2| |main::$tmp::tmp_if_expr_1|)
       (= |main::$tmp::return_value_nondet_int$0_2| |main::$tmp::return_value_nondet_int$0_1|)
       (= |main::$tmp::return_value_nondet_int$1_2| |main::$tmp::return_value_nondet_int$1_1|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int_2|) |main::1::L_1|)
       (= |main::1::i_2| |main::1::i_1|)
       (= |main::$tmp::tmp_if_expr_1| |main::$tmp::tmp_if_expr|)
       (= |main::$tmp::return_value_nondet_int$1_1| |main::$tmp::return_value_nondet_int$1|)
       (= |main::1::L_1| |main::1::L|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$0_1|) |main::1::i|)) 
    (|inv_14| |main::$tmp::tmp_if_expr| |main::$tmp::return_value_nondet_int$1| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_14| |main::$tmp::tmp_if_expr| |main::$tmp::return_value_nondet_int$1| |main::1::L| |main::1::i| |alloc_0| |memor_0|)
       (not (and (bvugt |main::1::L| (_ bv10 64))
       (bvult |main::1::i| |main::1::L|)))) true)))

(declare-fun |inv_13| (Bool (_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_14| |main::$tmp::tmp_if_expr| |main::$tmp::return_value_nondet_int$1| |main::1::L| |main::1::i| |alloc_0| |memor_0|)
       (and (bvugt |main::1::L| (_ bv10 64))
       (bvult |main::1::i| |main::1::L|))) 
    (|inv_13| |main::$tmp::tmp_if_expr| |main::$tmp::return_value_nondet_int$1| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_12| (Bool (_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_2| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_2| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_13| |main::$tmp::tmp_if_expr| |main::$tmp::return_value_nondet_int$1| |main::1::i| |alloc_2| |memor_2|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv6053561456450 64)) (store (select |memor_1| (select |alloc_0| (_ bv6053561456450 64))) |main::1::i| (_ bv1 64))))
       (= |memor_1| (store |memor_2| (select |alloc_0| (_ bv9363835545496 64)) (store (select |memor_2| (select |alloc_0| (_ bv9363835545496 64))) |main::1::i| (_ bv0 64))))
       (= |alloc_0| (store |alloc_1| (_ bv6053561456450 64) (_ bv6053561456450 64)))
       (= |alloc_1| (store |alloc_2| (_ bv9363835545496 64) (_ bv9363835545496 64)))) 
    (|inv_12| |main::$tmp::tmp_if_expr| |main::$tmp::return_value_nondet_int$1| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_10| (Bool (_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> 
    (|inv_12| |main::$tmp::tmp_if_expr| |main::$tmp::return_value_nondet_int$1| |main::1::i| |alloc_0| |memor_0|) 
    (|inv_10| |main::$tmp::tmp_if_expr| |main::$tmp::return_value_nondet_int$1| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_11| (Bool (_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_12| |main::$tmp::tmp_if_expr| |main::$tmp::return_value_nondet_int$1| |main::1::i| |alloc_0| |memor_0|)
       (not (not (= |main::$tmp::return_value_nondet_int$1| (_ bv0 32))))) 
    (|inv_11| |main::$tmp::tmp_if_expr| |main::$tmp::return_value_nondet_int$1| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_8| (Bool (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_11| |main::$tmp::tmp_if_expr| |main::$tmp::return_value_nondet_int$1| |main::1::i| |alloc_1| |memor_0|)
       (= |alloc_0| (store |alloc_1| (_ bv6907487098696 64) (select |alloc_1| (_ bv6053561456450 64))))) 
    (|inv_8| |main::$tmp::tmp_if_expr| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_9| (Bool (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_10| |main::$tmp::tmp_if_expr| |main::$tmp::return_value_nondet_int$1| |main::1::i| |alloc_0| |memor_0|)
       (not (= |main::$tmp::return_value_nondet_int$1| (_ bv0 32)))) 
    (|inv_9| |main::$tmp::tmp_if_expr| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_9| |main::$tmp::tmp_if_expr| |main::1::i| |alloc_1| |memor_0|)
       (= |alloc_0| (store |alloc_1| (_ bv6907487098696 64) (select |alloc_1| (_ bv9363835545496 64))))) 
    (|inv_8| |main::$tmp::tmp_if_expr| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_7| (Bool (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_8| |main::$tmp::tmp_if_expr| |main::1::i| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv6907487098696 64)) (store (select |memor_1| (select |alloc_0| (_ bv6907487098696 64))) |main::1::i| (bvadd (select (select |memor_1| (select |alloc_0| (_ bv6907487098696 64))) |main::1::i|) (_ bv1 64)))))) 
    (|inv_7| |main::$tmp::tmp_if_expr| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_5| (Bool (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool) (|main::1::i| (_ BitVec 64)))
  (=> 
    (|inv_7| |main::$tmp::tmp_if_expr| |main::1::i| |alloc_0| |memor_0|) 
    (|inv_5| |main::$tmp::tmp_if_expr| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_6| (Bool (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_7| |main::$tmp::tmp_if_expr| |main::1::i| |alloc_0| |memor_0|)
       (not (= (select (select |memor_0| (select |alloc_0| (_ bv6907487098696 64))) |main::1::i|) (_ bv1 64)))) 
    (|inv_6| |main::$tmp::tmp_if_expr| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_3| (Bool (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool) (|main::$tmp::tmp_if_expr_1| Bool) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)))
  (=> (and 
    (|inv_6| |main::$tmp::tmp_if_expr_1| |main::1::i_1| |alloc_0| |memor_0|)
       (= (ite (= (select (select |memor_0| (select |alloc_0| (_ bv6907487098696 64))) |main::1::i_1|) (_ bv2 64)) true false) |main::$tmp::tmp_if_expr|)
       (= |main::1::i_1| |main::1::i|)) 
    (|inv_3| |main::$tmp::tmp_if_expr| |alloc_0| |memor_0|))))

(declare-fun |inv_4| (Bool (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_5| |main::$tmp::tmp_if_expr| |main::1::i| |alloc_0| |memor_0|)
       (= (select (select |memor_0| (select |alloc_0| (_ bv6907487098696 64))) |main::1::i|) (_ bv1 64))) 
    (|inv_4| |main::$tmp::tmp_if_expr| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool) (|main::$tmp::tmp_if_expr_1| Bool))
  (=> (and 
    (|inv_4| |main::$tmp::tmp_if_expr_1| |alloc_0| |memor_0|)
       (= true |main::$tmp::tmp_if_expr|)) 
    (|inv_3| |main::$tmp::tmp_if_expr| |alloc_0| |memor_0|))))

(declare-fun |inv_2| (Bool (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool))
  (=> 
    (|inv_3| |main::$tmp::tmp_if_expr| |alloc_0| |memor_0|) 
    (|inv_2| |main::$tmp::tmp_if_expr| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool))
  (=> (and 
    (|inv_2| |main::$tmp::tmp_if_expr| |alloc_0| |memor_0|)
       (not |main::$tmp::tmp_if_expr|)) false)))

(declare-fun |inv_1| ((Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::tmp_if_expr| Bool))
  (=> (and 
    (|inv_2| |main::$tmp::tmp_if_expr| |alloc_0| |memor_0|)
       |main::$tmp::tmp_if_expr|) 
    (|inv_1| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))))
  (=> 
    (|inv_1| |alloc_0| |memor_0|) true)))

(check-sat)