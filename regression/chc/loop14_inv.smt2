; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)

(declare-fun |inv_30| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> true 
    (|inv_30| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_27| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_1| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::1::y_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)))
  (=> (and 
    (|inv_30| |main::$tmp::return_value_nondet_int_1| |main::$tmp::return_value_nondet_int$0_1| |main::1::1::y_1| |main::1::x_1|)
       (= |main::$tmp::return_value_nondet_int_1| |main::$tmp::return_value_nondet_int|)
       (= |main::$tmp::return_value_nondet_int$0_1| |main::$tmp::return_value_nondet_int$0|)
       (= |main::1::1::y_1| |main::1::1::y|)
       (= (_ bv0 32) |main::1::x|)) 
    (|inv_27| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_8| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> 
    (|inv_8| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|) 
    (|inv_27| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_25| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_27| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|)
       (not (= |main::$tmp::return_value_nondet_int| (_ bv0 32)))) 
    (|inv_25| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_26| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_27| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|)
       (= |main::$tmp::return_value_nondet_int| (_ bv0 32))) 
    (|inv_26| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_2| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> 
    (|inv_26| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|) 
    (|inv_2| |main::1::x|))))

(declare-fun |inv_23| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_1| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::1::y_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)))
  (=> (and 
    (|inv_25| |main::$tmp::return_value_nondet_int_1| |main::$tmp::return_value_nondet_int$0_1| |main::1::1::y_1| |main::1::x_1|)
       (= |main::$tmp::return_value_nondet_int_1| |main::$tmp::return_value_nondet_int|)
       (= |main::$tmp::return_value_nondet_int$0_1| |main::$tmp::return_value_nondet_int$0|)
       (= |main::$tmp::return_value_nondet_int$0_1| |main::1::1::y|)
       (= |main::1::x_1| |main::1::x|)) 
    (|inv_23| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_13| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_23| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|)
       (not (and (bvsge |main::1::x| (_ bv0 32))
       (not (bvsge |main::1::x| (_ bv10 32)))))) 
    (|inv_13| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_16| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_23| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|)
       (and (bvsge |main::1::x| (_ bv0 32))
       (not (bvsge |main::1::x| (_ bv10 32))))) 
    (|inv_16| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_19| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_16| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|)
       (not (and (bvsge |main::1::1::y| (_ bv0 32))
       (not (bvsge |main::1::1::y| (_ bv10 32)))))) 
    (|inv_19| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_17| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_19| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|)
       (not (and (bvsge |main::1::1::y| (_ bv4294967286 32))
       (not (bvsge |main::1::1::y| (_ bv1 32)))))) 
    (|inv_17| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_18| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_19| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|)
       (and (bvsge |main::1::1::y| (_ bv4294967286 32))
       (not (bvsge |main::1::1::y| (_ bv1 32))))) 
    (|inv_18| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_1| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::1::y_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)))
  (=> (and 
    (|inv_18| |main::$tmp::return_value_nondet_int_1| |main::$tmp::return_value_nondet_int$0_1| |main::1::1::y_1| |main::1::x_1|)
       (= |main::$tmp::return_value_nondet_int_1| |main::$tmp::return_value_nondet_int|)
       (= |main::$tmp::return_value_nondet_int$0_1| |main::$tmp::return_value_nondet_int$0|)
       (= |main::1::1::y_1| |main::1::1::y|)
       (= (bvsub |main::1::x_1| |main::1::1::y_1|) |main::1::x|)) 
    (|inv_17| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_14| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> 
    (|inv_17| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|) 
    (|inv_14| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_15| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_16| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|)
       (and (bvsge |main::1::1::y| (_ bv0 32))
       (not (bvsge |main::1::1::y| (_ bv10 32))))) 
    (|inv_15| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0_1| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int_1| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::1::y_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)))
  (=> (and 
    (|inv_15| |main::$tmp::return_value_nondet_int_1| |main::$tmp::return_value_nondet_int$0_1| |main::1::1::y_1| |main::1::x_1|)
       (= |main::$tmp::return_value_nondet_int_1| |main::$tmp::return_value_nondet_int|)
       (= |main::$tmp::return_value_nondet_int$0_1| |main::$tmp::return_value_nondet_int$0|)
       (= |main::1::1::y_1| |main::1::1::y|)
       (= (bvadd |main::1::x_1| |main::1::1::y_1|) |main::1::x|)) 
    (|inv_14| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> 
    (|inv_14| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|) 
    (|inv_13| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> 
    (|inv_13| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|) 
    (|inv_8| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_3| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::$tmp::return_value_nondet_int| (_ BitVec 32)) (|main::$tmp::return_value_nondet_int$0| (_ BitVec 32)) (|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> 
    (|inv_8| |main::$tmp::return_value_nondet_int| |main::$tmp::return_value_nondet_int$0| |main::1::1::y| |main::1::x|) 
    (|inv_3| |main::1::x|))))

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_3| |main::1::x|)
       (not true)) 
    (|inv_2| |main::1::x|))))

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_2| |main::1::x|)
       (not (bvsge |main::1::x| (_ bv0 32)))) false)))

(declare-fun |inv_1| () Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_2| |main::1::x|)
       (bvsge |main::1::x| (_ bv0 32))) 
    |inv_1|)))

(assert (=> 
    |inv_1| true))

(check-sat)