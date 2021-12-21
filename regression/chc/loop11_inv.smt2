; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)

(declare-fun |inv_16| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> true 
    (|inv_16| |main::$tmp::return_value_nondet_int| |main::1::x| |main::1::y|))))

(declare-fun |inv_14| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_2| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::x_2| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)) (|main::1::y_1| (_ BitVec 32)) (|main::1::y_2| (_ BitVec 32)))
  (=> (and 
    (|inv_16| |main::$tmp::return_value_nondet_int_2| |main::1::x_2| |main::1::y_2|)
       (= |main::$tmp::return_value_nondet_int_2| |main::$tmp::return_value_nondet_int_1|)
       (= (_ bv10 32) |main::1::x_1|)
       (= |main::1::y_2| |main::1::y_1|)
       (= |main::1::x_1| |main::1::x|)
       (= |main::$tmp::return_value_nondet_int_1| |main::1::y|)) 
    (|inv_14| |main::1::x| |main::1::y|))))

(declare-fun |inv_15| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_14| |main::1::x| |main::1::y|)
       (not (bvsge |main::1::y| (_ bv1 32)))) 
    (|inv_15| |main::1::x| |main::1::y|))))

(declare-fun |inv_1| () Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> 
    (|inv_15| |main::1::x| |main::1::y|) 
    |inv_1|)))

(declare-fun |inv_6| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_14| |main::1::x| |main::1::y|)
       (bvsge |main::1::y| (_ bv1 32))) 
    (|inv_6| |main::1::x| |main::1::y|))))

(declare-fun |inv_10| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_6| |main::1::x| |main::1::y|)
       (bvsge |main::1::x| (_ bv1 32))) 
    (|inv_10| |main::1::x| |main::1::y|))))

(declare-fun |inv_11| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_10| |main::1::x| |main::1::y|)
       (not (not (bvsge |main::1::y| |main::1::x|)))) 
    (|inv_11| |main::1::x| |main::1::y|))))

(declare-fun |inv_8| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)) (|main::1::y_1| (_ BitVec 32)))
  (=> (and 
    (|inv_11| |main::1::x_1| |main::1::y_1|)
       (= (bvsub |main::1::x_1| (_ bv1 32)) |main::1::x|)
       (= |main::1::y_1| |main::1::y|)) 
    (|inv_8| |main::1::x| |main::1::y|))))

(declare-fun |inv_9| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_10| |main::1::x| |main::1::y|)
       (not (bvsge |main::1::y| |main::1::x|))) 
    (|inv_9| |main::1::x| |main::1::y|))))

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)) (|main::1::y_1| (_ BitVec 32)))
  (=> (and 
    (|inv_9| |main::1::x_1| |main::1::y_1|)
       (= (bvsub |main::1::x_1| |main::1::y_1|) |main::1::x|)
       (= |main::1::y_1| |main::1::y|)) 
    (|inv_8| |main::1::x| |main::1::y|))))

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> 
    (|inv_8| |main::1::x| |main::1::y|) 
    (|inv_6| |main::1::x| |main::1::y|))))

(declare-fun |inv_4| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> 
    (|inv_6| |main::1::x| |main::1::y|) 
    (|inv_4| |main::1::x|))))

(declare-fun |inv_3| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_4| |main::1::x|)
       (not (bvsge |main::1::x| (_ bv1 32)))) 
    (|inv_3| |main::1::x|))))

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_3| |main::1::x|)
       (not (= |main::1::x| (_ bv0 32)))) false)))

(declare-fun |inv_2| () Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_3| |main::1::x|)
       (= |main::1::x| (_ bv0 32))) 
    |inv_2|)))

(assert (=> 
    |inv_2| 
    |inv_1|))

(assert (=> 
    |inv_1| true))

(check-sat)