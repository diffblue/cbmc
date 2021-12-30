; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)

; find_symbols
(declare-fun |tmp| () (_ BitVec 64))
(declare-fun |inv_25| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (= |alloc_0| ((as const (Array (_ BitVec 64) (_ BitVec 64)))(_ bv0 64))) 
    (|inv_25| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::$tmp::return_value_nondet_int$1| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::L| |main::1::i| |main::1::j| |alloc_0| |memor_0|))))

(declare-fun |inv_24| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$1_3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$2_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$2_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$2_3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3_3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4_3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_3| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::tmp_1| (_ BitVec 32)) (|main::1::tmp_2| (_ BitVec 32)) (|main::1::tmp_3| (_ BitVec 32)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)) (|main::1::L_2| (_ BitVec 64)) (|main::1::L_3| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)) (|main::1::i_2| (_ BitVec 64)) (|main::1::i_3| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)) (|main::1::j_1| (_ BitVec 64)) (|main::1::j_2| (_ BitVec 64)) (|main::1::j_3| (_ BitVec 64)))
  (=> (and 
    (|inv_25| |main::$tmp::return_value_nondet_int_3| |main::$tmp::return_value_nondet_int$0_3| |main::$tmp::return_value_nondet_int$1_3| |main::$tmp::return_value_nondet_int$2_3| |main::$tmp::return_value_nondet_int$3_3| |main::$tmp::return_value_nondet_int$4_3| |main::1::tmp_3| |main::1::L_3| |main::1::i_3| |main::1::j_3| |alloc_0| |memor_0|)
       (= |main::$tmp::return_value_nondet_int$0_3| |main::$tmp::return_value_nondet_int$0_2|)
       (= |main::$tmp::return_value_nondet_int$1_3| |main::$tmp::return_value_nondet_int$1_2|)
       (= |main::$tmp::return_value_nondet_int$2_3| |main::$tmp::return_value_nondet_int$2_2|)
       (= |main::$tmp::return_value_nondet_int$3_3| |main::$tmp::return_value_nondet_int$3_2|)
       (= |main::$tmp::return_value_nondet_int$4_3| |main::$tmp::return_value_nondet_int$4_2|)
       (= |main::1::tmp_3| |main::1::tmp_2|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int_3|) |main::1::L_2|)
       (= |main::1::i_3| |main::1::i_2|)
       (= |main::1::j_3| |main::1::j_2|)
       (= |main::$tmp::return_value_nondet_int$1_2| |main::$tmp::return_value_nondet_int$1_1|)
       (= |main::$tmp::return_value_nondet_int$2_2| |main::$tmp::return_value_nondet_int$2_1|)
       (= |main::$tmp::return_value_nondet_int$3_2| |main::$tmp::return_value_nondet_int$3_1|)
       (= |main::$tmp::return_value_nondet_int$4_2| |main::$tmp::return_value_nondet_int$4_1|)
       (= |main::1::tmp_2| |main::1::tmp_1|)
       (= |main::1::L_2| |main::1::L_1|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$0_2|) |main::1::i_1|)
       (= |main::1::j_2| |main::1::j_1|)
       (= |main::$tmp::return_value_nondet_int$2_1| |main::$tmp::return_value_nondet_int$2|)
       (= |main::$tmp::return_value_nondet_int$3_1| |main::$tmp::return_value_nondet_int$3|)
       (= |main::$tmp::return_value_nondet_int$4_1| |main::$tmp::return_value_nondet_int$4|)
       (= |main::1::tmp_1| |main::1::tmp|)
       (= |main::1::L_1| |main::1::L|)
       (= |main::1::i_1| |main::1::i|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$1_1|) |main::1::j|)) 
    (|inv_24| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::L| |main::1::i| |main::1::j| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_24| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::L| |main::1::i| |main::1::j| |alloc_0| |memor_0|)
       (not (and (and (bvugt |main::1::L| (_ bv10 64))
       (bvult |main::1::i| |main::1::L|))
       (bvult |main::1::j| |main::1::L|)))) true)))

(declare-fun |inv_23| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::j| (_ BitVec 64)))
  (=> (and 
    (|inv_24| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::L| |main::1::i| |main::1::j| |alloc_0| |memor_0|)
       (and (and (bvugt |main::1::L| (_ bv10 64))
       (bvult |main::1::i| |main::1::L|))
       (bvult |main::1::j| |main::1::L|))) 
    (|inv_23| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_22| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> 
    (|inv_23| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|) 
    (|inv_22| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_20| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> 
    (|inv_22| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|) 
    (|inv_20| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_21| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_22| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|)
       (not (not (= |main::$tmp::return_value_nondet_int$2| (_ bv0 32))))) 
    (|inv_21| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_18| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$2_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4_1| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::tmp_1| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)))
  (=> (and 
    (|inv_21| |main::$tmp::return_value_nondet_int$2_1| |main::$tmp::return_value_nondet_int$3_1| |main::$tmp::return_value_nondet_int$4_1| |main::1::tmp_1| |main::1::i_1| |alloc_1| |memor_0|)
       (= |alloc_0| (store |alloc_1| (_ bv6053561456450 64) (_ bv6053561456450 64)))
       (= |main::$tmp::return_value_nondet_int$2_1| |main::$tmp::return_value_nondet_int$2|)
       (= |main::$tmp::return_value_nondet_int$3_1| |main::$tmp::return_value_nondet_int$3|)
       (= |main::$tmp::return_value_nondet_int$4_1| |main::$tmp::return_value_nondet_int$4|)
       (= (_ bv0 32) |main::1::tmp|)
       (= |main::1::i_1| |main::1::i|)) 
    (|inv_18| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_19| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_20| |main::$tmp::return_value_nondet_int$2| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|)
       (not (= |main::$tmp::return_value_nondet_int$2| (_ bv0 32)))) 
    (|inv_19| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$3_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4_1| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::tmp_1| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)))
  (=> (and 
    (|inv_19| |main::$tmp::return_value_nondet_int$3_1| |main::$tmp::return_value_nondet_int$4_1| |main::1::tmp_1| |main::1::i_1| |alloc_0| |memor_0|)
       (= |main::$tmp::return_value_nondet_int$3_1| |main::$tmp::return_value_nondet_int$3|)
       (= |main::$tmp::return_value_nondet_int$4_1| |main::$tmp::return_value_nondet_int$4|)
       (= (_ bv1 32) |main::1::tmp|)
       (= |main::1::i_1| |main::1::i|)) 
    (|inv_18| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_17| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> 
    (|inv_18| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|) 
    (|inv_17| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_11| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> 
    (|inv_17| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|) 
    (|inv_11| |main::$tmp::return_value_nondet_int$3| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_16| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_17| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|)
       (not (not (= |main::1::tmp| (_ bv0 32))))) 
    (|inv_16| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_16| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::i| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv6053561456450 64)) (store (select |memor_1| (select |alloc_0| (_ bv6053561456450 64))) |main::1::i| ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$4|))))
       (= (select |alloc_0| (_ bv6053561456450 64)) (_ bv0 64))) false)))

(declare-fun |inv_14| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$4| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_16| |main::$tmp::return_value_nondet_int$3| |main::$tmp::return_value_nondet_int$4| |main::1::tmp| |main::1::i| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv6053561456450 64)) (store (select |memor_1| (select |alloc_0| (_ bv6053561456450 64))) |main::1::i| ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$4|))))) 
    (|inv_14| |main::$tmp::return_value_nondet_int$3| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_14| |main::$tmp::return_value_nondet_int$3| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|)
       (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv6053561456450 64))) |main::1::i|) (_ bv1 64)))
       (= (select |alloc_0| (_ bv6053561456450 64)) (_ bv0 64))) false)))

(declare-fun |inv_12| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_14| |main::$tmp::return_value_nondet_int$3| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|)
       (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv6053561456450 64))) |main::1::i|) (_ bv1 64)))) 
    (|inv_12| |main::$tmp::return_value_nondet_int$3| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_14| |main::$tmp::return_value_nondet_int$3| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|)
       (bvsge (select (select |memor_0| (select |alloc_0| (_ bv6053561456450 64))) |main::1::i|) (_ bv1 64))
       (= (select |alloc_0| (_ bv6053561456450 64)) (_ bv0 64))) false)))

(declare-fun |inv_13| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_14| |main::$tmp::return_value_nondet_int$3| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|)
       (bvsge (select (select |memor_0| (select |alloc_0| (_ bv6053561456450 64))) |main::1::i|) (_ bv1 64))) 
    (|inv_13| |main::$tmp::return_value_nondet_int$3| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_13| |main::$tmp::return_value_nondet_int$3| |main::1::tmp| |main::1::i| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv6053561456450 64)) (store (select |memor_1| (select |alloc_0| (_ bv6053561456450 64))) |main::1::i| (bvneg (select (select |memor_1| (select |alloc_0| (_ bv6053561456450 64))) |main::1::i|)))))
       (or (= (select |alloc_0| (_ bv6053561456450 64)) (_ bv0 64)) (= (select |alloc_0| (_ bv6053561456450 64)) (_ bv0 64)))) false)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_13| |main::$tmp::return_value_nondet_int$3| |main::1::tmp| |main::1::i| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv6053561456450 64)) (store (select |memor_1| (select |alloc_0| (_ bv6053561456450 64))) |main::1::i| (bvneg (select (select |memor_1| (select |alloc_0| (_ bv6053561456450 64))) |main::1::i|)))))) 
    (|inv_12| |main::$tmp::return_value_nondet_int$3| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_5| ((_ BitVec 32) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> 
    (|inv_12| |main::$tmp::return_value_nondet_int$3| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|) 
    (|inv_5| |main::1::tmp| |alloc_0| |memor_0|))))

(declare-fun |inv_10| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_11| |main::$tmp::return_value_nondet_int$3| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|)
       (not (= |main::1::tmp| (_ bv0 32)))) 
    (|inv_10| |main::$tmp::return_value_nondet_int$3| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_10| |main::$tmp::return_value_nondet_int$3| |main::1::tmp| |main::1::i| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv9363835545496 64)) (store (select |memor_1| (select |alloc_0| (_ bv9363835545496 64))) |main::1::i| ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$3|))))
       (= (select |alloc_0| (_ bv9363835545496 64)) (_ bv0 64))) false)))

(declare-fun |inv_8| ((_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$3| (_ BitVec 32)) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_10| |main::$tmp::return_value_nondet_int$3| |main::1::tmp| |main::1::i| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv9363835545496 64)) (store (select |memor_1| (select |alloc_0| (_ bv9363835545496 64))) |main::1::i| ((_ sign_extend 32) |main::$tmp::return_value_nondet_int$3|))))) 
    (|inv_8| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_8| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|)
       (not (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv9363835545496 64))) |main::1::i|) (_ bv0 64))))
       (= (select |alloc_0| (_ bv9363835545496 64)) (_ bv0 64))) false)))

(declare-fun |inv_9| ((_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_8| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|)
       (not (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv9363835545496 64))) |main::1::i|) (_ bv0 64))))) 
    (|inv_9| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_6| ((_ BitVec 32) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> 
    (|inv_9| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|) 
    (|inv_6| |main::1::tmp| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_8| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|)
       (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv9363835545496 64))) |main::1::i|) (_ bv0 64)))
       (= (select |alloc_0| (_ bv9363835545496 64)) (_ bv0 64))) false)))

(declare-fun |inv_7| ((_ BitVec 32) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_8| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|)
       (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv9363835545496 64))) |main::1::i|) (_ bv0 64)))) 
    (|inv_7| |main::1::tmp| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_7| |main::1::tmp| |main::1::i| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv9363835545496 64)) (store (select |memor_1| (select |alloc_0| (_ bv9363835545496 64))) |main::1::i| (bvneg (select (select |memor_1| (select |alloc_0| (_ bv9363835545496 64))) |main::1::i|)))))
       (or (= (select |alloc_0| (_ bv9363835545496 64)) (_ bv0 64)) (= (select |alloc_0| (_ bv9363835545496 64)) (_ bv0 64)))) false)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 32)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_7| |main::1::tmp| |main::1::i| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv9363835545496 64)) (store (select |memor_1| (select |alloc_0| (_ bv9363835545496 64))) |main::1::i| (bvneg (select (select |memor_1| (select |alloc_0| (_ bv9363835545496 64))) |main::1::i|)))))) 
    (|inv_6| |main::1::tmp| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 32)))
  (=> 
    (|inv_6| |main::1::tmp| |alloc_0| |memor_0|) 
    (|inv_5| |main::1::tmp| |alloc_0| |memor_0|))))

(declare-fun |inv_4| ((_ BitVec 32) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 32)))
  (=> 
    (|inv_5| |main::1::tmp| |alloc_0| |memor_0|) 
    (|inv_4| |main::1::tmp| |alloc_0| |memor_0|))))

(declare-fun |inv_2| ((_ BitVec 32) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 32)))
  (=> 
    (|inv_4| |main::1::tmp| |alloc_0| |memor_0|) 
    (|inv_2| |main::1::tmp| |alloc_0| |memor_0|))))

(declare-fun |inv_3| ((_ BitVec 32) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 32)))
  (=> (and 
    (|inv_4| |main::1::tmp| |alloc_0| |memor_0|)
       (not (not (= |main::1::tmp| (_ bv0 32))))) 
    (|inv_3| |main::1::tmp| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 32)))
  (=> (and 
    (|inv_3| |main::1::tmp| |alloc_1| |memor_0|)
       (= |alloc_0| (store |alloc_1| (_ bv9363835545496 64) (select |alloc_1| (_ bv6053561456450 64))))
       (= (select |alloc_1| (_ bv6053561456450 64)) (_ bv0 64))) false)))

(declare-fun |inv_1| ((Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 32)))
  (=> (and 
    (|inv_3| |main::1::tmp| |alloc_1| |memor_0|)
       (= |alloc_0| (store |alloc_1| (_ bv9363835545496 64) (select |alloc_1| (_ bv6053561456450 64))))) 
    (|inv_1| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 32)))
  (=> (and 
    (|inv_2| |main::1::tmp| |alloc_1| |memor_0|)
       (= |alloc_0| (store |alloc_1| (_ bv6053561456450 64) (select |alloc_1| (_ bv9363835545496 64))))
       (not (= |main::1::tmp| (_ bv0 32)))
       (= (select |alloc_1| (_ bv9363835545496 64)) (_ bv0 64))) false)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::tmp| (_ BitVec 32)))
  (=> (and 
    (|inv_2| |main::1::tmp| |alloc_1| |memor_0|)
       (= |alloc_0| (store |alloc_1| (_ bv6053561456450 64) (select |alloc_1| (_ bv9363835545496 64))))
       (not (= |main::1::tmp| (_ bv0 32)))) 
    (|inv_1| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))))
  (=> 
    (|inv_1| |alloc_0| |memor_0|) true)))

(check-sat)