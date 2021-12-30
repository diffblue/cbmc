; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)

; find_symbols
(declare-fun |tmp| () (_ BitVec 64))
(declare-fun |inv_8| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (= |alloc_0| ((as const (Array (_ BitVec 64) (_ BitVec 64)))(_ bv0 64))) 
    (|inv_8| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_7| ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::$tmp::return_value_nondet_int$0_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_2| (_ BitVec 32)) (|main::1::L| (_ BitVec 64)) (|main::1::L_1| (_ BitVec 64)) (|main::1::L_2| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)) (|main::1::i_1| (_ BitVec 64)) (|main::1::i_2| (_ BitVec 64)))
  (=> (and 
    (|inv_8| |main::$tmp::return_value_nondet_int_2| |main::$tmp::return_value_nondet_int$0_2| |main::1::L_2| |main::1::i_2| |alloc_0| |memor_0|)
       (= |main::$tmp::return_value_nondet_int$0_2| |main::$tmp::return_value_nondet_int$0_1|)
       (= ((_ sign_extend 32) |main::$tmp::return_value_nondet_int_2|) |main::1::L_1|)
       (= |main::1::i_2| |main::1::i_1|)
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
       (not (and (bvuge |main::1::L| (_ bv2 64))
       (not (bvuge (bvadd |main::1::i| (_ bv1 64)) |main::1::L|))))) 
    (|inv_6| |main::1::L| |main::1::i| |alloc_0| |memor_0|))))

(declare-fun |inv_1| ((Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> 
    (|inv_6| |main::1::L| |main::1::i| |alloc_0| |memor_0|) 
    (|inv_1| |alloc_0| |memor_0|))))

(declare-fun |inv_4| ((_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::L| (_ BitVec 64)) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_5| |main::1::L| |main::1::i| |alloc_0| |memor_0|)
       (and (bvuge |main::1::L| (_ bv2 64))
       (not (bvuge (bvadd |main::1::i| (_ bv1 64)) |main::1::L|)))) 
    (|inv_4| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_2| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_2| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_4| |main::1::i| |alloc_2| |memor_2|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv1393540289558 64)) (store (select |memor_1| (select |alloc_0| (_ bv1393540289558 64))) (bvadd |main::1::i| (_ bv1 64)) (bvadd (select (select |memor_1| (select |alloc_0| (_ bv1393540289558 64))) |main::1::i|) (_ bv8 64)))))
       (= |alloc_0| (store |alloc_1| (_ bv1393540289558 64) (select |alloc_1| (_ bv6808354179106 64))))
       (= |memor_1| (store |memor_2| (select |alloc_1| (_ bv6808354179106 64)) (store (select |memor_2| (select |alloc_1| (_ bv6808354179106 64))) |main::1::i| (_ bv53 64))))
       (= |alloc_1| (store |alloc_2| (_ bv6808354179106 64) (_ bv6808354179106 64)))
       (or (= (select |alloc_0| (_ bv1393540289558 64)) (_ bv0 64)) (= (select |alloc_0| (_ bv1393540289558 64)) (_ bv0 64)) (= (select |alloc_1| (_ bv6808354179106 64)) (_ bv0 64)))) false)))

(declare-fun |inv_3| ((_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_1| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|memor_2| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_1| (Array (_ BitVec 64) (_ BitVec 64))) (|alloc_2| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_4| |main::1::i| |alloc_2| |memor_2|)
       (= |memor_0| (store |memor_1| (select |alloc_0| (_ bv1393540289558 64)) (store (select |memor_1| (select |alloc_0| (_ bv1393540289558 64))) (bvadd |main::1::i| (_ bv1 64)) (bvadd (select (select |memor_1| (select |alloc_0| (_ bv1393540289558 64))) |main::1::i|) (_ bv8 64)))))
       (= |alloc_0| (store |alloc_1| (_ bv1393540289558 64) (select |alloc_1| (_ bv6808354179106 64))))
       (= |memor_1| (store |memor_2| (select |alloc_1| (_ bv6808354179106 64)) (store (select |memor_2| (select |alloc_1| (_ bv6808354179106 64))) |main::1::i| (_ bv53 64))))
       (= |alloc_1| (store |alloc_2| (_ bv6808354179106 64) (_ bv6808354179106 64)))) 
    (|inv_3| |main::1::i| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_3| |main::1::i| |alloc_0| |memor_0|)
       (not (bvsgt (select (select |memor_0| (select |alloc_0| (_ bv6808354179106 64))) (bvadd |main::1::i| (_ bv1 64))) (select (select |memor_0| (select |alloc_0| (_ bv6808354179106 64))) |main::1::i|)))
       (= (select |alloc_0| (_ bv6808354179106 64)) (_ bv0 64))) false)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_3| |main::1::i| |alloc_0| |memor_0|)
       (not (bvsgt (select (select |memor_0| (select |alloc_0| (_ bv6808354179106 64))) (bvadd |main::1::i| (_ bv1 64))) (select (select |memor_0| (select |alloc_0| (_ bv6808354179106 64))) |main::1::i|)))) false)))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_3| |main::1::i| |alloc_0| |memor_0|)
       (bvsgt (select (select |memor_0| (select |alloc_0| (_ bv6808354179106 64))) (bvadd |main::1::i| (_ bv1 64))) (select (select |memor_0| (select |alloc_0| (_ bv6808354179106 64))) |main::1::i|))
       (= (select |alloc_0| (_ bv6808354179106 64)) (_ bv0 64))) false)))

(declare-fun |inv_2| ((Array (_ BitVec 64) (_ BitVec 64)) (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))) ) Bool)

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))) (|main::1::i| (_ BitVec 64)))
  (=> (and 
    (|inv_3| |main::1::i| |alloc_0| |memor_0|)
       (bvsgt (select (select |memor_0| (select |alloc_0| (_ bv6808354179106 64))) (bvadd |main::1::i| (_ bv1 64))) (select (select |memor_0| (select |alloc_0| (_ bv6808354179106 64))) |main::1::i|))) 
    (|inv_2| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))))
  (=> 
    (|inv_2| |alloc_0| |memor_0|) 
    (|inv_1| |alloc_0| |memor_0|))))

(assert (forall ((|memor_0| (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))) (|alloc_0| (Array (_ BitVec 64) (_ BitVec 64))))
  (=> 
    (|inv_1| |alloc_0| |memor_0|) true)))

(check-sat)