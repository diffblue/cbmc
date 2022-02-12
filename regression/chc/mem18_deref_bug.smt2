; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)
; var_id: main::1::y; 2
; var_id: main::1::x; 1

; find_symbols
(declare-fun |tmp| () (_ BitVec 64))
(declare-fun |inv_8| ((_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (= |alloc_0| ((as const (Array (_ BitVec 64) (_ BitVec 64))) (_ bv0 64))) 
    (|inv_8| |main::$tmp::return_value_nondet_int| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_1| ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int_2| (_ BitVec 32)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)) (|main::1::L_2| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)) (|main::1::i_2| (_ BitVec 64)))
  (=> (and 
    (|inv_8| |main::$tmp::return_value_nondet_int_2| |main::1::L_2| |main::1::i_2| |alloc_1| |memor_0|)
       (= |alloc_0| (store |alloc_1| (_ bv1 64) (_ bv1 64)))
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int_2|) |main::1::L_1|)
       (= |main::1::i_2| |main::1::i_1|)
       (= |main::1::L_1| |main::1::L|)
       (= (_ bv0 64) |main::1::i|)) 
    (|inv_1| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_5| ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_1| |main::1::L| |main::1::i| |alloc_0| |memor_0|)
       (not (bvuge |main::1::i| |main::1::L|))) 
    (|inv_5| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_5| |main::1::L| |main::1::i| |alloc_0| |memor_0|)
       (not (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::i|) (_ bv0 64))))
       (= (select |alloc_0| (_ bv1 64)) (_ bv0 64))) false)))

(declare-fun |inv_3| ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_5| |main::1::L| |main::1::i| |alloc_0| |memor_0|)
       (not (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::i|) (_ bv0 64))))) 
    (|inv_3| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_5| |main::1::L| |main::1::i| |alloc_0| |memor_0|)
       (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::i|) (_ bv0 64)))
       (= (select |alloc_0| (_ bv1 64)) (_ bv0 64))) false)))

(declare-fun |inv_4| ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_5| |main::1::L| |main::1::i| |alloc_0| |memor_0|)
       (not (bvsge (select (select |memor_0| (select |alloc_0| (_ bv1 64))) |main::1::i|) (_ bv0 64)))) 
    (|inv_4| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> 
    (|inv_4| |main::1::L| |main::1::i| |alloc_0| |memor_0|) true)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)))
  (=> (and 
    (|inv_3| |main::1::L_1| |main::1::i_1| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv2 64)) (store (select |memor_1| (select |alloc_0| (_ bv2 64))) |main::1::i_1| (select (select |memor_1| (select |alloc_0| (_ bv1 64))) |main::1::i_1|))))
       (= |main::1::L_1| |main::1::L|)
       (= (bvadd |main::1::i_1| (_ bv1 64)) |main::1::i|)
       (or (= (select |alloc_0| (_ bv1 64)) (_ bv0 64)) (= (select |alloc_0| (_ bv2 64)) (_ bv0 64)))) false)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)))
  (=> (and 
    (|inv_3| |main::1::L_1| |main::1::i_1| |alloc_0| |memor_1|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv2 64)) (store (select |memor_1| (select |alloc_0| (_ bv2 64))) |main::1::i_1| (select (select |memor_1| (select |alloc_0| (_ bv1 64))) |main::1::i_1|))))
       (= |main::1::L_1| |main::1::L|)
       (= (bvadd |main::1::i_1| (_ bv1 64)) |main::1::i|)) 
    (|inv_1| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_1| |main::1::L| |main::1::i| |alloc_0| |memor_0|)
       (not (not (bvuge |main::1::i| |main::1::L|)))) true)))

(check-sat)