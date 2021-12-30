; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)

; find_symbols
(declare-fun |tmp| () (_ BitVec 64))
(declare-fun |inv_7| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::1::t1| (_ BitVec 64)) (|main::1::1::t2| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (= |alloc_0| ((as const (Array (_ BitVec 64) (_ BitVec 64)))(_ bv0 64))) 
    (|inv_7| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::$tmp::return_value_nondet_int$1| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::1::t1| |main::1::1::t2| |main::1::L| |main::1::i| |main::1::j| |alloc_0| |memor_0|))))

(declare-fun |inv_6| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1_3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$2_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$2_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$2_3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3_3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4_3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_3| (_ BitVec 32)) (|main::1::1::t1| (_ BitVec 64)) (|main::1::1::t1_1| (_ BitVec 64)) (|main::1::1::t1_2| (_ BitVec 64)) (|main::1::1::t1_3| (_ BitVec 64)) (|main::1::1::t2| (_ BitVec 64)) (|main::1::1::t2_1| (_ BitVec 64)) (|main::1::1::t2_2| (_ BitVec 64)) (|main::1::1::t2_3| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)) (|main::1::L_2| (_ BitVec 64)) (|main::1::L_3| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)) (|main::1::i_2| (_ BitVec 64)) (|main::1::i_3| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)) (|main::1::j_1| (_ BitVec 64)) (|main::1::j_2| (_ BitVec 64)) (|main::1::j_3| (_ BitVec 64)))
  (=> (and 
    (|inv_7| |main::$tmp::return_value_nondet_int_3| |main::$tmp::return_value_nondet_int$0_3| |main::$tmp::return_value_nondet_int$1_3| |main::$tmp::return_value_nondet_int$2_3| |main::$tmp::return_value_nondet_int$3_3| |main::$tmp::return_value_nondet_int$4_3| |main::1::1::t1_3| |main::1::1::t2_3| |main::1::L_3| |main::1::i_3| |main::1::j_3| |alloc_0| |memor_0|)
       (= |main::$tmp::return_value_nondet_int$0_3| |main::$tmp::return_value_nondet_int$0_2|)
       (= |main::$tmp::return_value_nondet_int$1_3| |main::$tmp::return_value_nondet_int$1_2|)
       (= |main::$tmp::return_value_nondet_int$2_3| |main::$tmp::return_value_nondet_int$2_2|)
       (= |main::$tmp::return_value_nondet_int$3_3| |main::$tmp::return_value_nondet_int$3_2|)
       (= |main::$tmp::return_value_nondet_int$4_3| |main::$tmp::return_value_nondet_int$4_2|)
       (= |main::1::1::t1_3| |main::1::1::t1_2|)
       (= |main::1::1::t2_3| |main::1::1::t2_2|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int_3|) |main::1::L_2|)
       (= |main::1::i_3| |main::1::i_2|)
       (= |main::1::j_3| |main::1::j_2|)
       (= |main::$tmp::return_value_nondet_int$1_2| |main::$tmp::return_value_nondet_int$1_1|)
       (= |main::$tmp::return_value_nondet_int$2_2| |main::$tmp::return_value_nondet_int$2_1|)
       (= |main::$tmp::return_value_nondet_int$3_2| |main::$tmp::return_value_nondet_int$3_1|)
       (= |main::$tmp::return_value_nondet_int$4_2| |main::$tmp::return_value_nondet_int$4_1|)
       (= |main::1::1::t1_2| |main::1::1::t1_1|)
       (= |main::1::1::t2_2| |main::1::1::t2_1|)
       (= |main::1::L_2| |main::1::L_1|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$0_2|) |main::1::i_1|)
       (= |main::1::j_2| |main::1::j_1|)
       (= |main::$tmp::return_value_nondet_int$2_1| |main::$tmp::return_value_nondet_int$2|)
       (= |main::$tmp::return_value_nondet_int$3_1| |main::$tmp::return_value_nondet_int$3|)
       (= |main::$tmp::return_value_nondet_int$4_1| |main::$tmp::return_value_nondet_int$4|)
       (= |main::1::1::t1_1| |main::1::1::t1|)
       (= |main::1::1::t2_1| |main::1::1::t2|)
       (= |main::1::L_1| |main::1::L|)
       (= |main::1::i_1| |main::1::i|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$1_1|) |main::1::j|)) 
    (|inv_6| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::1::t1| |main::1::1::t2| |main::1::L| |main::1::i| |main::1::j| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::1::t1| (_ BitVec 64)) (|main::1::1::t2| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_6| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::1::t1| |main::1::1::t2| |main::1::L| |main::1::i| |main::1::j| |alloc_0| |memor_0|)
       (not (and (and (bvugt |main::1::L| (_ bv10 64))
       (bvult |main::1::i| |main::1::L|))
       (bvult |main::1::j| |main::1::L|)))) true)))

(declare-fun |inv_5| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::1::t1| (_ BitVec 64)) (|main::1::1::t2| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_6| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::1::t1| |main::1::1::t2| |main::1::L| |main::1::i| |main::1::j| |alloc_0| |memor_0|)
       (and (and (bvugt |main::1::L| (_ bv10 64))
       (bvult |main::1::i| |main::1::L|))
       (bvult |main::1::j| |main::1::L|))) 
    (|inv_5| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::1::t1| |main::1::1::t2| |main::1::i| |main::1::j| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_2| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_2| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::1::t1| (_ BitVec 64)) (|main::1::1::t2| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_5| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::1::t1| |main::1::1::t2| |main::1::i| |main::1::j| |alloc_2| |memor_2|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv6053561456450 64)) (store (select |memor_1| (select |alloc_0| (_ bv6053561456450 64))) |main::1::j| ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$3|))))
       (= |memor_1| (store |memor_2| (select |alloc_0| (_ bv9363835545496 64)) (store (select |memor_2| (select |alloc_0| (_ bv9363835545496 64))) |main::1::i| ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$2|))))
       (= |alloc_0| (store |alloc_1| (_ bv6053561456450 64) (_ bv6053561456450 64)))
       (= |alloc_1| (store |alloc_2| (_ bv9363835545496 64) (_ bv9363835545496 64)))
       (or (= (select |alloc_0| (_ bv6053561456450 64)) (_ bv0 64)) (= (select |alloc_0| (_ bv9363835545496 64)) (_ bv0 64)))) false)))

(declare-fun |inv_3| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_2| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_2| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::1::t1| (_ BitVec 64)) (|main::1::1::t2| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_5| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::1::t1| |main::1::1::t2| |main::1::i| |main::1::j| |alloc_2| |memor_2|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv6053561456450 64)) (store (select |memor_1| (select |alloc_0| (_ bv6053561456450 64))) |main::1::j| ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$3|))))
       (= |memor_1| (store |memor_2| (select |alloc_0| (_ bv9363835545496 64)) (store (select |memor_2| (select |alloc_0| (_ bv9363835545496 64))) |main::1::i| ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$2|))))
       (= |alloc_0| (store |alloc_1| (_ bv6053561456450 64) (_ bv6053561456450 64)))
       (= |alloc_1| (store |alloc_2| (_ bv9363835545496 64) (_ bv9363835545496 64)))) 
    (|inv_3| |main::$tmp::return_value_nondet_int$4| |main::1::1::t1| |main::1::1::t2| |main::1::i| |main::1::j| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::1::t1| (_ BitVec 64)) (|main::1::1::t2| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_3| |main::$tmp::return_value_nondet_int$4| |main::1::1::t1| |main::1::1::t2| |main::1::i| |main::1::j| |alloc_0| |memor_0|)
       (not (= (select (select |memor_0| (select |alloc_0| (_ bv9363835545496 64))) |main::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv6053561456450 64))) |main::1::j|)))
       (or (= (select |alloc_0| (_ bv6053561456450 64)) (_ bv0 64)) (= (select |alloc_0| (_ bv9363835545496 64)) (_ bv0 64)))) false)))

(declare-fun |inv_4| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::1::t1| (_ BitVec 64)) (|main::1::1::t2| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_3| |main::$tmp::return_value_nondet_int$4| |main::1::1::t1| |main::1::1::t2| |main::1::i| |main::1::j| |alloc_0| |memor_0|)
       (not (= (select (select |memor_0| (select |alloc_0| (_ bv9363835545496 64))) |main::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv6053561456450 64))) |main::1::j|)))) 
    (|inv_4| |main::$tmp::return_value_nondet_int$4| |main::1::1::t1| |main::1::1::t2| |main::1::i| |main::1::j| |alloc_0| |memor_0|))))

(declare-fun |inv_1| ((Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::1::t1| (_ BitVec 64)) (|main::1::1::t2| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> 
    (|inv_4| |main::$tmp::return_value_nondet_int$4| |main::1::1::t1| |main::1::1::t2| |main::1::i| |main::1::j| |alloc_0| |memor_0|) 
    (|inv_1| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::1::t1| (_ BitVec 64)) (|main::1::1::t2| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_3| |main::$tmp::return_value_nondet_int$4| |main::1::1::t1| |main::1::1::t2| |main::1::i| |main::1::j| |alloc_0| |memor_0|)
       (= (select (select |memor_0| (select |alloc_0| (_ bv9363835545496 64))) |main::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv6053561456450 64))) |main::1::j|))
       (or (= (select |alloc_0| (_ bv6053561456450 64)) (_ bv0 64)) (= (select |alloc_0| (_ bv9363835545496 64)) (_ bv0 64)))) false)))

(declare-fun |inv_2| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::1::t1| (_ BitVec 64)) (|main::1::1::t2| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_3| |main::$tmp::return_value_nondet_int$4| |main::1::1::t1| |main::1::1::t2| |main::1::i| |main::1::j| |alloc_0| |memor_0|)
       (= (select (select |memor_0| (select |alloc_0| (_ bv9363835545496 64))) |main::1::i|) (select (select |memor_0| (select |alloc_0| (_ bv6053561456450 64))) |main::1::j|))) 
    (|inv_2| |main::$tmp::return_value_nondet_int$4| |main::1::1::t1| |main::1::1::t2| |main::1::i| |main::1::j| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_2| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_3| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_4| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$4_2| (_ BitVec 32)) (|main::1::1::t1| (_ BitVec 64)) (|main::1::1::t1_1| (_ BitVec 64)) (|main::1::1::t1_2| (_ BitVec 64)) (|main::1::1::t2| (_ BitVec 64)) (|main::1::1::t2_1| (_ BitVec 64)) (|main::1::1::t2_2| (_ BitVec 64)) (|main::1::i_2| (_ BitVec 64)) (|main::1::j_1| (_ BitVec 64)) (|main::1::j_2| (_ BitVec 64)))
  (=> (and 
    (|inv_2| |main::$tmp::return_value_nondet_int$4_2| |main::1::1::t1_2| |main::1::1::t2_2| |main::1::i_2| |main::1::j_2| |alloc_1| |memor_4|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv6053561456450 64)) (store (select |memor_1| (select |alloc_0| (_ bv6053561456450 64))) (_ bv0 64) |main::1::1::t2|)))
       (= |memor_1| (store |memor_2| (select |alloc_0| (_ bv9363835545496 64)) (store (select |memor_2| (select |alloc_0| (_ bv9363835545496 64))) (_ bv0 64) |main::1::1::t1|)))
       (= |alloc_0| (store |alloc_1| (_ bv620109269044 64) (select |alloc_1| (_ bv6053561456450 64))))
       (= |memor_2| (store |memor_3| (select |alloc_1| (_ bv6053561456450 64)) (store (select |memor_3| (select |alloc_1| (_ bv6053561456450 64))) |main::1::i_2| (select (select |memor_3| (select |alloc_1| (_ bv9363835545496 64))) |main::1::j_2|))))
       (= |memor_3| (store |memor_4| (select |alloc_1| (_ bv9363835545496 64)) (store (select |memor_4| (select |alloc_1| (_ bv9363835545496 64))) |main::1::j_2| ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$4_2|))))
       (= (bvadd (select (select |memor_2| (select |alloc_0| (_ bv6907487098696 64))) |main::1::i_2|) (select (select |memor_2| (select |alloc_0| (_ bv620109269044 64))) |main::1::i_2|)) |main::1::1::t1_1|)
       (= |main::1::1::t2_2| |main::1::1::t2_1|)
       (= |main::1::j_2| |main::1::j_1|)
       (= |main::1::1::t1_1| |main::1::1::t1|)
       (= (bvadd (select (select |memor_2| (select |alloc_0| (_ bv6907487098696 64))) |main::1::j_1|) (select (select |memor_2| (select |alloc_0| (_ bv620109269044 64))) |main::1::j_1|)) |main::1::1::t2|)
       (or (= (select |alloc_0| (_ bv6053561456450 64)) (_ bv0 64)) (= (select |alloc_0| (_ bv6907487098696 64)) (_ bv0 64)) (= (select |alloc_0| (_ bv9363835545496 64)) (_ bv0 64)) (= (select |alloc_0| (_ bv620109269044 64)) (_ bv0 64)) (= (select |alloc_1| (_ bv6053561456450 64)) (_ bv0 64)) (= (select |alloc_1| (_ bv9363835545496 64)) (_ bv0 64)) (= (select |alloc_1| (_ bv9363835545496 64)) (_ bv0 64)))) false)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_2| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_3| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_4| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$4_2| (_ BitVec 32)) (|main::1::1::t1| (_ BitVec 64)) (|main::1::1::t1_1| (_ BitVec 64)) (|main::1::1::t1_2| (_ BitVec 64)) (|main::1::1::t2| (_ BitVec 64)) (|main::1::1::t2_1| (_ BitVec 64)) (|main::1::1::t2_2| (_ BitVec 64)) (|main::1::i_2| (_ BitVec 64)) (|main::1::j_1| (_ BitVec 64)) (|main::1::j_2| (_ BitVec 64)))
  (=> (and 
    (|inv_2| |main::$tmp::return_value_nondet_int$4_2| |main::1::1::t1_2| |main::1::1::t2_2| |main::1::i_2| |main::1::j_2| |alloc_1| |memor_4|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv6053561456450 64)) (store (select |memor_1| (select |alloc_0| (_ bv6053561456450 64))) (_ bv0 64) |main::1::1::t2|)))
       (= |memor_1| (store |memor_2| (select |alloc_0| (_ bv9363835545496 64)) (store (select |memor_2| (select |alloc_0| (_ bv9363835545496 64))) (_ bv0 64) |main::1::1::t1|)))
       (= |alloc_0| (store |alloc_1| (_ bv620109269044 64) (select |alloc_1| (_ bv6053561456450 64))))
       (= |memor_2| (store |memor_3| (select |alloc_1| (_ bv6053561456450 64)) (store (select |memor_3| (select |alloc_1| (_ bv6053561456450 64))) |main::1::i_2| (select (select |memor_3| (select |alloc_1| (_ bv9363835545496 64))) |main::1::j_2|))))
       (= |memor_3| (store |memor_4| (select |alloc_1| (_ bv9363835545496 64)) (store (select |memor_4| (select |alloc_1| (_ bv9363835545496 64))) |main::1::j_2| ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$4_2|))))
       (= (bvadd (select (select |memor_2| (select |alloc_0| (_ bv6907487098696 64))) |main::1::i_2|) (select (select |memor_2| (select |alloc_0| (_ bv620109269044 64))) |main::1::i_2|)) |main::1::1::t1_1|)
       (= |main::1::1::t2_2| |main::1::1::t2_1|)
       (= |main::1::j_2| |main::1::j_1|)
       (= |main::1::1::t1_1| |main::1::1::t1|)
       (= (bvadd (select (select |memor_2| (select |alloc_0| (_ bv6907487098696 64))) |main::1::j_1|) (select (select |memor_2| (select |alloc_0| (_ bv620109269044 64))) |main::1::j_1|)) |main::1::1::t2|)) 
    (|inv_1| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))))
  (=> 
    (|inv_1| |alloc_0| |memor_0|) true)))

(check-sat)