; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)

; find_symbols
(declare-fun |tmp| () (_ BitVec 64))
(declare-fun |inv_14| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::tmp| (_ BitVec 64)))
  (=> (= |alloc_0| ((as const (Array (_ BitVec 64) (_ BitVec 64)))(_ bv0 64))) 
    (|inv_14| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::$tmp::return_value_nondet_int$1| |main::1::L| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|))))

(declare-fun |inv_13| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_2| (_ BitVec 32)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)) (|main::1::L_2| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)) (|main::1::i_2| (_ BitVec 64)) (|main::1::tmp| (_ BitVec 64)) (|main::1::tmp_1| (_ BitVec 64)) (|main::1::tmp_2| (_ BitVec 64)))
  (=> (and 
    (|inv_14| |main::$tmp::return_value_nondet_int_2| |main::$tmp::return_value_nondet_int$0_2| |main::$tmp::return_value_nondet_int$1_2| |main::1::L_2| |main::1::i_2| |main::1::tmp_2| |alloc_0| |memor_0|)
       (= |main::$tmp::return_value_nondet_int$0_2| |main::$tmp::return_value_nondet_int$0_1|)
       (= |main::$tmp::return_value_nondet_int$1_2| |main::$tmp::return_value_nondet_int$1_1|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int_2|) |main::1::L_1|)
       (= |main::1::i_2| |main::1::i_1|)
       (= |main::1::tmp_2| |main::1::tmp_1|)
       (= |main::$tmp::return_value_nondet_int$1_1| |main::$tmp::return_value_nondet_int$1|)
       (= |main::1::L_1| |main::1::L|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$0_1|) |main::1::i|)
       (= |main::1::tmp_1| |main::1::tmp|)) 
    (|inv_13| |main::$tmp::return_value_nondet_int$1| |main::1::L| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::tmp| (_ BitVec 64)))
  (=> (and 
    (|inv_13| |main::$tmp::return_value_nondet_int$1| |main::1::L| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|)
       (not (and (bvugt |main::1::L| (_ bv10 64))
       (bvult |main::1::i| |main::1::L|)))) true)))

(declare-fun |inv_12| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::tmp| (_ BitVec 64)))
  (=> (and 
    (|inv_13| |main::$tmp::return_value_nondet_int$1| |main::1::L| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|)
       (and (bvugt |main::1::L| (_ bv10 64))
       (bvult |main::1::i| |main::1::L|))) 
    (|inv_12| |main::$tmp::return_value_nondet_int$1| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|))))

(declare-fun |inv_11| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)) (|main::1::tmp| (_ BitVec 64)))
  (=> 
    (|inv_12| |main::$tmp::return_value_nondet_int$1| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|) 
    (|inv_11| |main::$tmp::return_value_nondet_int$1| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|))))

(declare-fun |inv_9| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)) (|main::1::tmp| (_ BitVec 64)))
  (=> 
    (|inv_11| |main::$tmp::return_value_nondet_int$1| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|) 
    (|inv_9| |main::$tmp::return_value_nondet_int$1| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|))))

(declare-fun |inv_10| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)) (|main::1::tmp| (_ BitVec 64)))
  (=> (and 
    (|inv_11| |main::$tmp::return_value_nondet_int$1| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|)
       (not (not (= |main::$tmp::return_value_nondet_int$1| (_ bv0 32))))) 
    (|inv_10| |main::$tmp::return_value_nondet_int$1| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_2| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1_1| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)) (|main::1::tmp| (_ BitVec 64)) (|main::1::tmp_1| (_ BitVec 64)))
  (=> (and 
    (|inv_10| |main::$tmp::return_value_nondet_int$1_1| |main::1::i_1| |main::1::tmp_1| |alloc_2| |memor_1|)
       (= |alloc_0| (store |alloc_1| (_ bv6907487098696 64) (select |alloc_1| (_ bv6053561456450 64))))
       (= |memor_0| (store |memor_1| (select |alloc_1| (_ bv6053561456450 64)) (store (select |memor_1| (select |alloc_1| (_ bv6053561456450 64))) |main::1::i_1| (_ bv8 64))))
       (= |alloc_1| (store |alloc_2| (_ bv6053561456450 64) (_ bv6053561456450 64)))
       (= |main::$tmp::return_value_nondet_int$1_1| |main::$tmp::return_value_nondet_int$1|)
       (= |main::1::i_1| |main::1::i|)
       (= (_ bv0 64) |main::1::tmp|)
       (= (select |alloc_1| (_ bv6053561456450 64)) (_ bv0 64))) false)))

(declare-fun |inv_7| ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_2| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1_1| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)) (|main::1::tmp| (_ BitVec 64)) (|main::1::tmp_1| (_ BitVec 64)))
  (=> (and 
    (|inv_10| |main::$tmp::return_value_nondet_int$1_1| |main::1::i_1| |main::1::tmp_1| |alloc_2| |memor_1|)
       (= |alloc_0| (store |alloc_1| (_ bv6907487098696 64) (select |alloc_1| (_ bv6053561456450 64))))
       (= |memor_0| (store |memor_1| (select |alloc_1| (_ bv6053561456450 64)) (store (select |memor_1| (select |alloc_1| (_ bv6053561456450 64))) |main::1::i_1| (_ bv8 64))))
       (= |alloc_1| (store |alloc_2| (_ bv6053561456450 64) (_ bv6053561456450 64)))
       (= |main::$tmp::return_value_nondet_int$1_1| |main::$tmp::return_value_nondet_int$1|)
       (= |main::1::i_1| |main::1::i|)
       (= (_ bv0 64) |main::1::tmp|)) 
    (|inv_7| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|))))

(declare-fun |inv_8| ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)) (|main::1::tmp| (_ BitVec 64)))
  (=> (and 
    (|inv_9| |main::$tmp::return_value_nondet_int$1| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|)
       (not (= |main::$tmp::return_value_nondet_int$1| (_ bv0 32)))) 
    (|inv_8| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_2| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)) (|main::1::tmp| (_ BitVec 64)) (|main::1::tmp_1| (_ BitVec 64)))
  (=> (and 
    (|inv_8| |main::1::i_1| |main::1::tmp_1| |alloc_2| |memor_1|)
       (= |alloc_0| (store |alloc_1| (_ bv6907487098696 64) (select |alloc_1| (_ bv9363835545496 64))))
       (= |memor_0| (store |memor_1| (select |alloc_1| (_ bv9363835545496 64)) (store (select |memor_1| (select |alloc_1| (_ bv9363835545496 64))) |main::1::i_1| (_ bv5 64))))
       (= |alloc_1| (store |alloc_2| (_ bv9363835545496 64) (_ bv9363835545496 64)))
       (= |main::1::i_1| |main::1::i|)
       (= (_ bv1 64) |main::1::tmp|)
       (= (select |alloc_1| (_ bv9363835545496 64)) (_ bv0 64))) false)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_2| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)) (|main::1::tmp| (_ BitVec 64)) (|main::1::tmp_1| (_ BitVec 64)))
  (=> (and 
    (|inv_8| |main::1::i_1| |main::1::tmp_1| |alloc_2| |memor_1|)
       (= |alloc_0| (store |alloc_1| (_ bv6907487098696 64) (select |alloc_1| (_ bv9363835545496 64))))
       (= |memor_0| (store |memor_1| (select |alloc_1| (_ bv9363835545496 64)) (store (select |memor_1| (select |alloc_1| (_ bv9363835545496 64))) |main::1::i_1| (_ bv5 64))))
       (= |alloc_1| (store |alloc_2| (_ bv9363835545496 64) (_ bv9363835545496 64)))
       (= |main::1::i_1| |main::1::i|)
       (= (_ bv1 64) |main::1::tmp|)) 
    (|inv_7| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|))))

(declare-fun |inv_6| ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)) (|main::1::tmp| (_ BitVec 64)))
  (=> 
    (|inv_7| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|) 
    (|inv_6| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)) (|main::1::tmp| (_ BitVec 64)))
  (=> (and 
    (|inv_6| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|)
       (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv6907487098696 64))) |main::1::i|) (_ bv5 64)))
       (= (select |alloc_0| (_ bv6907487098696 64)) (_ bv0 64))) false)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)) (|main::1::tmp| (_ BitVec 64)))
  (=> (and 
    (|inv_6| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|)
       (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv6907487098696 64))) |main::1::i|) (_ bv5 64)))) false)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)) (|main::1::tmp| (_ BitVec 64)))
  (=> (and 
    (|inv_6| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|)
       (bvsge (select (select |memor_0| (select |alloc_0| (_ bv6907487098696 64))) |main::1::i|) (_ bv5 64))
       (= (select |alloc_0| (_ bv6907487098696 64)) (_ bv0 64))) false)))

(declare-fun |inv_5| ((_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)) (|main::1::tmp| (_ BitVec 64)))
  (=> (and 
    (|inv_6| |main::1::i| |main::1::tmp| |alloc_0| |memor_0|)
       (bvsge (select (select |memor_0| (select |alloc_0| (_ bv6907487098696 64))) |main::1::i|) (_ bv5 64))) 
    (|inv_5| |main::1::tmp| |alloc_0| |memor_0|))))

(declare-fun |inv_4| ((_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 64)))
  (=> 
    (|inv_5| |main::1::tmp| |alloc_0| |memor_0|) 
    (|inv_4| |main::1::tmp| |alloc_0| |memor_0|))))

(declare-fun |inv_2| ((_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 64)))
  (=> 
    (|inv_4| |main::1::tmp| |alloc_0| |memor_0|) 
    (|inv_2| |main::1::tmp| |alloc_0| |memor_0|))))

(declare-fun |inv_3| ((_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 64)))
  (=> (and 
    (|inv_4| |main::1::tmp| |alloc_0| |memor_0|)
       (not (not (= |main::1::tmp| (_ bv0 64))))) 
    (|inv_3| |main::1::tmp| |alloc_0| |memor_0|))))

(declare-fun |inv_1| ((Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 64)))
  (=> 
    (|inv_3| |main::1::tmp| |alloc_0| |memor_0|) 
    (|inv_1| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 64)))
  (=> (and 
    (|inv_2| |main::1::tmp| |alloc_0| |memor_0|)
       (not (= |main::1::tmp| (_ bv0 64)))) 
    (|inv_1| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))))
  (=> 
    (|inv_1| |alloc_0| |memor_0|) true)))

(check-sat)