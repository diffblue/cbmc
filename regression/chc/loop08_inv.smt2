; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)

(declare-fun |inv_18| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> true 
    (|inv_18| |main::$tmp::return_value_nondet_int| |main::1::1::i| |main::1::x| |main::1::y|))))

(declare-fun |inv_4| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int_2| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_3| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::1::i_1| (_ BitVec 32)) (|main::1::1::i_2| (_ BitVec 32)) (|main::1::1::i_3| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::x_2| (_ BitVec 32)) (|main::1::x_3| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)) (|main::1::y_1| (_ BitVec 32)) (|main::1::y_2| (_ BitVec 32)) (|main::1::y_3| (_ BitVec 32)))
  (=> (and 
    (|inv_18| |main::$tmp::return_value_nondet_int_3| |main::1::1::i_3| |main::1::x_3| |main::1::y_3|)
       (= |main::$tmp::return_value_nondet_int_3| |main::$tmp::return_value_nondet_int_2|)
       (= |main::1::1::i_3| |main::1::1::i_2|)
       (= (_ bv0 32) |main::1::x_2|)
       (= |main::1::y_3| |main::1::y_2|)
       (= |main::1::1::i_2| |main::1::1::i_1|)
       (= |main::1::x_2| |main::1::x_1|)
       (= |main::$tmp::return_value_nondet_int_2| |main::1::y_1|)
       (= (_ bv0 32) |main::1::1::i|)
       (= |main::1::x_1| |main::1::x|)
       (= |main::1::y_1| |main::1::y|)) 
    (|inv_4| |main::1::1::i| |main::1::x| |main::1::y|))))

(declare-fun |inv_15| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::i| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_4| |main::1::1::i| |main::1::x| |main::1::y|)
       (not (bvsge |main::1::1::i| (_ bv10 32)))) 
    (|inv_15| |main::1::1::i| |main::1::x| |main::1::y|))))

(declare-fun |inv_7| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::i| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_15| |main::1::1::i| |main::1::x| |main::1::y|)
       (not (not (bvsge |main::1::y| (_ bv11 32))))) 
    (|inv_7| |main::1::1::i| |main::1::x| |main::1::y|))))

(declare-fun |inv_12| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::i| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_15| |main::1::1::i| |main::1::x| |main::1::y|)
       (not (bvsge |main::1::y| (_ bv11 32)))) 
    (|inv_12| |main::1::1::i| |main::1::x| |main::1::y|))))

(declare-fun |inv_8| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::i| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_12| |main::1::1::i| |main::1::x| |main::1::y|)
       (not (bvsge |main::1::y| (_ bv1 32)))) 
    (|inv_8| |main::1::1::i| |main::1::x| |main::1::y|))))

(declare-fun |inv_11| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::i| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_12| |main::1::1::i| |main::1::x| |main::1::y|)
       (bvsge |main::1::y| (_ bv1 32))) 
    (|inv_11| |main::1::1::i| |main::1::x| |main::1::y|))))

(declare-fun |inv_10| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::i| (_ BitVec 32)) (|main::1::1::i_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)) (|main::1::y_1| (_ BitVec 32)))
  (=> (and 
    (|inv_11| |main::1::1::i_1| |main::1::x_1| |main::1::y_1|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= (bvadd |main::1::x_1| |main::1::y_1|) |main::1::x|)
       (= |main::1::y_1| |main::1::y|)) 
    (|inv_10| |main::1::1::i| |main::1::x| |main::1::y|))))

(assert (forall ((|main::1::1::i| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_10| |main::1::1::i| |main::1::x| |main::1::y|)
       (not (bvsge |main::1::x| |main::1::1::i|))) false)))

(declare-fun |inv_9| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::i| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_10| |main::1::1::i| |main::1::x| |main::1::y|)
       (bvsge |main::1::x| |main::1::1::i|)) 
    (|inv_9| |main::1::1::i| |main::1::x| |main::1::y|))))

(assert (forall ((|main::1::1::i| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> 
    (|inv_9| |main::1::1::i| |main::1::x| |main::1::y|) 
    (|inv_8| |main::1::1::i| |main::1::x| |main::1::y|))))

(assert (forall ((|main::1::1::i| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> 
    (|inv_8| |main::1::1::i| |main::1::x| |main::1::y|) 
    (|inv_7| |main::1::1::i| |main::1::x| |main::1::y|))))

(assert (forall ((|main::1::1::i| (_ BitVec 32)) (|main::1::1::i_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)) (|main::1::y_1| (_ BitVec 32)))
  (=> (and 
    (|inv_7| |main::1::1::i_1| |main::1::x_1| |main::1::y_1|)
       (= (bvadd |main::1::1::i_1| (_ bv1 32)) |main::1::1::i|)
       (= |main::1::x_1| |main::1::x|)
       (= |main::1::y_1| |main::1::y|)) 
    (|inv_4| |main::1::1::i| |main::1::x| |main::1::y|))))

(declare-fun |inv_1| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::i| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> 
    (|inv_4| |main::1::1::i| |main::1::x| |main::1::y|) 
    (|inv_1| |main::1::1::i|))))

(assert (forall ((|main::1::1::i| (_ BitVec 32)))
  (=> (and 
    (|inv_1| |main::1::1::i|)
       (not (not (bvsge |main::1::1::i| (_ bv10 32))))) true)))

(check-sat)