; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)

; find_symbols
(declare-fun |tmp| () (_ BitVec 64))
(declare-fun |inv_7| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 64)) (|main::1::2::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (= |alloc_0| ((as const (Array (_ BitVec 64) (_ BitVec 64)))(_ bv0 64))) 
    (|inv_7| |main::$tmp::return_value_nondet_int| |main::1::1::i| |main::1::2::i| |main::1::L| |alloc_0| |memor_0|))))

(declare-fun |inv_6| ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int_1| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::2::i| (_ BitVec 64)) (|main::1::2::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_7| |main::$tmp::return_value_nondet_int_1| |main::1::1::i_1| |main::1::2::i_1| |main::1::L_1| |alloc_1| |memor_0|)
       (= |alloc_0| (store |alloc_1| (_ bv9363835545496 64) (_ bv9363835545496 64)))
       (= |main::1::1::i_1| |main::1::1::i|)
       (= |main::1::2::i_1| |main::1::2::i|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int_1|) |main::1::L|)) 
    (|inv_6| |main::1::1::i| |main::1::2::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::1::i| (_ BitVec 64)) (|main::1::2::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_6| |main::1::1::i| |main::1::2::i| |main::1::L| |alloc_0| |memor_0|)
       (not (bvugt |main::1::L| (_ bv0 64)))) true)))

(declare-fun |inv_5| ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::1::i| (_ BitVec 64)) (|main::1::2::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_6| |main::1::1::i| |main::1::2::i| |main::1::L| |alloc_0| |memor_0|)
       (bvugt |main::1::L| (_ bv0 64))) 
    (|inv_5| |main::1::1::i| |main::1::2::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::2::i| (_ BitVec 64)) (|main::1::2::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_5| |main::1::1::i_1| |main::1::2::i_1| |main::1::L_1| |alloc_1| |memor_0|)
       (= |alloc_0| (store |alloc_1| (_ bv6053561456450 64) (select |alloc_1| (_ bv9363835545496 64))))
       (= (_ bv0 64) |main::1::1::i|)
       (= |main::1::2::i_1| |main::1::2::i|)
       (= |main::1::L_1| |main::1::L|)
       (= (select |alloc_1| (_ bv9363835545496 64)) (_ bv0 64))) false)))

(declare-fun |inv_3| ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::2::i| (_ BitVec 64)) (|main::1::2::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_5| |main::1::1::i_1| |main::1::2::i_1| |main::1::L_1| |alloc_1| |memor_0|)
       (= |alloc_0| (store |alloc_1| (_ bv6053561456450 64) (select |alloc_1| (_ bv9363835545496 64))))
       (= (_ bv0 64) |main::1::1::i|)
       (= |main::1::2::i_1| |main::1::2::i|)
       (= |main::1::L_1| |main::1::L|)) 
    (|inv_3| |main::1::1::i| |main::1::2::i| |main::1::L| |alloc_0| |memor_0|))))

(declare-fun |inv_4| ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::1::i| (_ BitVec 64)) (|main::1::2::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_3| |main::1::1::i| |main::1::2::i| |main::1::L| |alloc_0| |memor_0|)
       (not (bvuge |main::1::1::i| |main::1::L|))) 
    (|inv_4| |main::1::1::i| |main::1::2::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::2::i| (_ BitVec 64)) (|main::1::2::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_4| |main::1::1::i_1| |main::1::2::i_1| |main::1::L_1| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv6053561456450 64)) (store (select |memor_1| (select |alloc_0| (_ bv6053561456450 64))) |main::1::1::i_1| (_ bv0 64))))
       (= (bvadd |main::1::1::i_1| (_ bv1 64)) |main::1::1::i|)
       (= |main::1::2::i_1| |main::1::2::i|)
       (= |main::1::L_1| |main::1::L|)
       (= (select |alloc_0| (_ bv6053561456450 64)) (_ bv0 64))) false)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::1::i| (_ BitVec 64)) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::2::i| (_ BitVec 64)) (|main::1::2::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_4| |main::1::1::i_1| |main::1::2::i_1| |main::1::L_1| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv6053561456450 64)) (store (select |memor_1| (select |alloc_0| (_ bv6053561456450 64))) |main::1::1::i_1| (_ bv0 64))))
       (= (bvadd |main::1::1::i_1| (_ bv1 64)) |main::1::1::i|)
       (= |main::1::2::i_1| |main::1::2::i|)
       (= |main::1::L_1| |main::1::L|)) 
    (|inv_3| |main::1::1::i| |main::1::2::i| |main::1::L| |alloc_0| |memor_0|))))

(declare-fun |inv_1| ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::1::i_1| (_ BitVec 64)) (|main::1::2::i| (_ BitVec 64)) (|main::1::2::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_3| |main::1::1::i_1| |main::1::2::i_1| |main::1::L_1| |alloc_0| |memor_0|)
       (not (not (bvuge |main::1::1::i_1| |main::1::L_1|)))
       (= (_ bv0 64) |main::1::2::i|)
       (= |main::1::L_1| |main::1::L|)) 
    (|inv_1| |main::1::2::i| |main::1::L| |alloc_0| |memor_0|))))

(declare-fun |inv_2| ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::2::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_1| |main::1::2::i| |main::1::L| |alloc_0| |memor_0|)
       (not (bvuge |main::1::2::i| |main::1::L|))) 
    (|inv_2| |main::1::2::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::2::i| (_ BitVec 64)) (|main::1::2::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_2| |main::1::2::i_1| |main::1::L_1| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv6907487098696 64)) (store (select |memor_1| (select |alloc_0| (_ bv6907487098696 64))) |main::1::2::i_1| (bvadd (select (select |memor_1| (select |alloc_0| (_ bv6907487098696 64))) |main::1::2::i_1|) (_ bv1 64)))))
       (= (bvadd |main::1::2::i_1| (_ bv1 64)) |main::1::2::i|)
       (= |main::1::L_1| |main::1::L|)
       (or (= (select |alloc_0| (_ bv6907487098696 64)) (_ bv0 64)) (= (select |alloc_0| (_ bv6907487098696 64)) (_ bv0 64)))) false)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::2::i| (_ BitVec 64)) (|main::1::2::i_1| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)))
  (=> (and 
    (|inv_2| |main::1::2::i_1| |main::1::L_1| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv6907487098696 64)) (store (select |memor_1| (select |alloc_0| (_ bv6907487098696 64))) |main::1::2::i_1| (bvadd (select (select |memor_1| (select |alloc_0| (_ bv6907487098696 64))) |main::1::2::i_1|) (_ bv1 64)))))
       (= (bvadd |main::1::2::i_1| (_ bv1 64)) |main::1::2::i|)
       (= |main::1::L_1| |main::1::L|)) 
    (|inv_1| |main::1::2::i| |main::1::L| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::2::i| (_ BitVec 64)) (|main::1::L| (_ BitVec 64)))
  (=> (and 
    (|inv_1| |main::1::2::i| |main::1::L| |alloc_0| |memor_0|)
       (not (not (bvuge |main::1::2::i| |main::1::L|)))) true)))

(check-sat)