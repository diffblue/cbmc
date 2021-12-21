; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)

(declare-fun |inv_9| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> true 
    (|inv_9| |main::$tmp::return_value_nondet_int| |main::1::x| |main::1::y|))))

(declare-fun |inv_7| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_2| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::x_2| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)) (|main::1::y_1| (_ BitVec 32)) (|main::1::y_2| (_ BitVec 32)))
  (=> (and 
    (|inv_9| |main::$tmp::return_value_nondet_int_2| |main::1::x_2| |main::1::y_2|)
       (= |main::$tmp::return_value_nondet_int_2| |main::$tmp::return_value_nondet_int_1|)
       (= (_ bv0 32) |main::1::x_1|)
       (= |main::1::y_2| |main::1::y_1|)
       (= |main::1::x_1| |main::1::x|)
       (= |main::$tmp::return_value_nondet_int_1| |main::1::y|)) 
    (|inv_7| |main::1::x| |main::1::y|))))

(declare-fun |inv_8| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_7| |main::1::x| |main::1::y|)
       (not (bvsge |main::1::y| (_ bv1 32)))) 
    (|inv_8| |main::1::x| |main::1::y|))))

(declare-fun |inv_1| () Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> 
    (|inv_8| |main::1::x| |main::1::y|) 
    |inv_1|)))

(declare-fun |inv_5| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_7| |main::1::x| |main::1::y|)
       (bvsge |main::1::y| (_ bv1 32))) 
    (|inv_5| |main::1::x| |main::1::y|))))

(declare-fun |inv_4| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_4| |main::1::x| |main::1::y|)
       (not (bvsge |main::1::x| (_ bv0 32)))) 
    (|inv_5| |main::1::x| |main::1::y|))))

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)) (|main::1::y_1| (_ BitVec 32)))
  (=> (and 
    (|inv_5| |main::1::x_1| |main::1::y_1|)
       (= (bvadd |main::1::x_1| (_ bv1 32)) |main::1::x|)
       (= |main::1::y_1| |main::1::y|)) 
    (|inv_4| |main::1::x| |main::1::y|))))

(declare-fun |inv_3| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_4| |main::1::x| |main::1::y|)
       (not (not (bvsge |main::1::x| (_ bv0 32))))) 
    (|inv_3| |main::1::x| |main::1::y|))))

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_3| |main::1::x| |main::1::y|)
       (not (bvsle |main::1::x| |main::1::y|))) false)))

(declare-fun |inv_2| () Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_3| |main::1::x| |main::1::y|)
       (bvsle |main::1::x| |main::1::y|)) 
    |inv_2|)))

(assert (=> 
    |inv_2| 
    |inv_1|))

(assert (=> 
    |inv_1| true))

(check-sat)