; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)

(declare-fun |inv_22| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::1::1::2::unused| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> true 
    (|inv_22| |main::$tmp::return_value_nondet_int| |main::1::1::2::unused| |main::1::x| |main::1::y|))))

(declare-fun |inv_21| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_2| (_ BitVec 32)) (|main::1::1::2::unused| (_ BitVec 32)) (|main::1::1::2::unused_1| (_ BitVec 32)) (|main::1::1::2::unused_2| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::x_2| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)) (|main::1::y_1| (_ BitVec 32)) (|main::1::y_2| (_ BitVec 32)))
  (=> (and 
    (|inv_22| |main::$tmp::return_value_nondet_int_2| |main::1::1::2::unused_2| |main::1::x_2| |main::1::y_2|)
       (= |main::$tmp::return_value_nondet_int_2| |main::$tmp::return_value_nondet_int_1|)
       (= |main::1::1::2::unused_2| |main::1::1::2::unused_1|)
       (= (_ bv0 32) |main::1::x_1|)
       (= |main::1::y_2| |main::1::y_1|)
       (= |main::1::1::2::unused_1| |main::1::1::2::unused|)
       (= |main::1::x_1| |main::1::x|)
       (= |main::$tmp::return_value_nondet_int_1| |main::1::y|)) 
    (|inv_21| |main::1::1::2::unused| |main::1::x| |main::1::y|))))

(assert (forall ((|main::1::1::2::unused| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_21| |main::1::1::2::unused| |main::1::x| |main::1::y|)
       (not (and (bvsle (bvneg (_ bv10 32)) |main::1::y|)
       (bvsle |main::1::y| (_ bv10 32))))) true)))

(declare-fun |inv_20| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::2::unused| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_21| |main::1::1::2::unused| |main::1::x| |main::1::y|)
       (and (bvsle (bvneg (_ bv10 32)) |main::1::y|)
       (bvsle |main::1::y| (_ bv10 32)))) 
    (|inv_20| |main::1::1::2::unused| |main::1::x| |main::1::y|))))

(declare-fun |inv_6| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::2::unused| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> 
    (|inv_20| |main::1::1::2::unused| |main::1::x| |main::1::y|) 
    (|inv_6| |main::1::1::2::unused| |main::1::x| |main::1::y|))))

(declare-fun |inv_11| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::2::unused| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> 
    (|inv_6| |main::1::1::2::unused| |main::1::x| |main::1::y|) 
    (|inv_11| |main::1::1::2::unused| |main::1::x| |main::1::y|))))

(declare-fun |inv_16| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::2::unused| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_11| |main::1::1::2::unused| |main::1::x| |main::1::y|)
       (not (not (bvsge |main::1::y| (_ bv0 32))))) 
    (|inv_16| |main::1::1::2::unused| |main::1::x| |main::1::y|))))

(declare-fun |inv_12| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::2::unused| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_16| |main::1::1::2::unused| |main::1::x| |main::1::y|)
       (not (bvsge |main::1::y| (_ bv1 32)))) 
    (|inv_12| |main::1::1::2::unused| |main::1::x| |main::1::y|))))

(declare-fun |inv_15| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::2::unused| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_16| |main::1::1::2::unused| |main::1::x| |main::1::y|)
       (bvsge |main::1::y| (_ bv1 32))) 
    (|inv_15| |main::1::1::2::unused| |main::1::x| |main::1::y|))))

(declare-fun |inv_14| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::2::unused| (_ BitVec 32)) (|main::1::1::2::unused_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)) (|main::1::y_1| (_ BitVec 32)))
  (=> (and 
    (|inv_15| |main::1::1::2::unused_1| |main::1::x_1| |main::1::y_1|)
       (= |main::1::1::2::unused_1| |main::1::1::2::unused|)
       (= (bvadd |main::1::x_1| |main::1::y_1|) |main::1::x|)
       (= |main::1::y_1| |main::1::y|)) 
    (|inv_14| |main::1::1::2::unused| |main::1::x| |main::1::y|))))

(assert (forall ((|main::1::1::2::unused| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_14| |main::1::1::2::unused| |main::1::x| |main::1::y|)
       (not (bvsgt |main::1::x| (_ bv0 32)))) false)))

(declare-fun |inv_13| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::2::unused| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_14| |main::1::1::2::unused| |main::1::x| |main::1::y|)
       (bvsgt |main::1::x| (_ bv0 32))) 
    (|inv_13| |main::1::1::2::unused| |main::1::x| |main::1::y|))))

(assert (forall ((|main::1::1::2::unused| (_ BitVec 32)) (|main::1::1::2::unused_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)) (|main::1::y_1| (_ BitVec 32)))
  (=> (and 
    (|inv_13| |main::1::1::2::unused_1| |main::1::x_1| |main::1::y_1|)
       (= |main::1::1::2::unused_1| |main::1::1::2::unused|)
       (= |main::1::x_1| |main::1::x|)
       (= (bvneg |main::1::y_1|) |main::1::y|)) 
    (|inv_6| |main::1::1::2::unused| |main::1::x| |main::1::y|))))

(declare-fun |inv_9| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::2::unused| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> 
    (|inv_12| |main::1::1::2::unused| |main::1::x| |main::1::y|) 
    (|inv_9| |main::1::1::2::unused| |main::1::x| |main::1::y|))))

(declare-fun |inv_10| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::2::unused| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_11| |main::1::1::2::unused| |main::1::x| |main::1::y|)
       (not (bvsge |main::1::y| (_ bv0 32)))) 
    (|inv_10| |main::1::1::2::unused| |main::1::x| |main::1::y|))))

(declare-fun |inv_2| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::2::unused| (_ BitVec 32)) (|main::1::1::2::unused_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)) (|main::1::y_1| (_ BitVec 32)))
  (=> (and 
    (|inv_10| |main::1::1::2::unused_1| |main::1::x_1| |main::1::y_1|)
       (= |main::1::1::2::unused_1| |main::1::1::2::unused|)
       (= (bvadd |main::1::x_1| (_ bv1 32)) |main::1::x|)
       (= |main::1::y_1| |main::1::y|)) 
    (|inv_2| |main::1::x|))))

(assert (forall ((|main::1::1::2::unused| (_ BitVec 32)) (|main::1::1::2::unused_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)) (|main::1::y_1| (_ BitVec 32)))
  (=> (and 
    (|inv_9| |main::1::1::2::unused_1| |main::1::x_1| |main::1::y_1|)
       (= |main::1::1::2::unused_1| |main::1::1::2::unused|)
       (= |main::1::x_1| |main::1::x|)
       (= (bvadd |main::1::y_1| (_ bv1 32)) |main::1::y|)) 
    (|inv_6| |main::1::1::2::unused| |main::1::x| |main::1::y|))))

(declare-fun |inv_3| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::2::unused| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> 
    (|inv_6| |main::1::1::2::unused| |main::1::x| |main::1::y|) 
    (|inv_3| |main::1::x|))))

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_3| |main::1::x|)
       (not true)) 
    (|inv_2| |main::1::x|))))

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_2| |main::1::x|)
       (not (bvsgt |main::1::x| (_ bv0 32)))) false)))

(declare-fun |inv_1| () Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_2| |main::1::x|)
       (bvsgt |main::1::x| (_ bv0 32))) 
    |inv_1|)))

(assert (=> 
    |inv_1| true))

(check-sat)