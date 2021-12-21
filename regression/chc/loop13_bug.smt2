; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)

(declare-fun |inv_18| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> true 
    (|inv_18| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_15| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_1| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::1::y_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)))
  (=> (and 
    (|inv_18| |main::$tmp::return_value_nondet_int_1| |main::$tmp::return_value_nondet_int$0_1| |main::1::1::y_1| |main::1::x_1|)
       (= |main::$tmp::return_value_nondet_int_1| |main::$tmp::return_value_nondet_int|)
       (= |main::$tmp::return_value_nondet_int$0_1| |main::$tmp::return_value_nondet_int$0|)
       (= |main::1::1::y_1| |main::1::1::y|)
       (= (_ bv0 32) |main::1::x|)) 
    (|inv_15| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_6| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> 
    (|inv_6| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|) 
    (|inv_15| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_13| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_15| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|)
       (not (= |main::$tmp::return_value_nondet_int| (_ bv0 32)))) 
    (|inv_13| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_14| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_15| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|)
       (= |main::$tmp::return_value_nondet_int| (_ bv0 32))) 
    (|inv_14| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_2| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> 
    (|inv_14| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|) 
    (|inv_2| |main::1::x|))))

(declare-fun |inv_11| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_1| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::1::y_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)))
  (=> (and 
    (|inv_13| |main::$tmp::return_value_nondet_int_1| |main::$tmp::return_value_nondet_int$0_1| |main::1::1::y_1| |main::1::x_1|)
       (= |main::$tmp::return_value_nondet_int_1| |main::$tmp::return_value_nondet_int|)
       (= |main::$tmp::return_value_nondet_int$0_1| |main::$tmp::return_value_nondet_int$0|)
       (= |main::$tmp::return_value_nondet_int$0_1| |main::1::1::y|)
       (= |main::1::x_1| |main::1::x|)) 
    (|inv_11| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_9| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_11| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|)
       (not (= |main::1::1::y| (_ bv1 32)))) 
    (|inv_9| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_10| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_11| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|)
       (= |main::1::1::y| (_ bv1 32))) 
    (|inv_10| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_1| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::1::y_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)))
  (=> (and 
    (|inv_10| |main::$tmp::return_value_nondet_int_1| |main::$tmp::return_value_nondet_int$0_1| |main::1::1::y_1| |main::1::x_1|)
       (= |main::$tmp::return_value_nondet_int_1| |main::$tmp::return_value_nondet_int|)
       (= |main::$tmp::return_value_nondet_int$0_1| |main::$tmp::return_value_nondet_int$0|)
       (= |main::1::1::y_1| |main::1::1::y|)
       (= (bvadd |main::1::x_1| |main::1::1::y_1|) |main::1::x|)) 
    (|inv_9| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> 
    (|inv_9| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|) 
    (|inv_6| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_3| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> 
    (|inv_6| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|) 
    (|inv_3| |main::1::x|))))

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_3| |main::1::x|)
       (not true)) 
    (|inv_2| |main::1::x|))))

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_2| |main::1::x|)
       (not (= |main::1::x| (_ bv0 32)))) false)))

(declare-fun |inv_1| () Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_2| |main::1::x|)
       (= |main::1::x| (_ bv0 32))) 
    |inv_1|)))

(assert (=> 
    |inv_1| true))

(check-sat)