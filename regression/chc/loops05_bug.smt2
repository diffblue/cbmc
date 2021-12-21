; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)

(declare-fun |inv_18| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> true 
    (|inv_18| |main::1::x|))))

(declare-fun |inv_3| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)))
  (=> (and 
    (|inv_18| |main::1::x_1|)
       (= (_ bv0 32) |main::1::x|)) 
    (|inv_3| |main::1::x|))))

(declare-fun |inv_17| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> 
    (|inv_3| |main::1::x|) 
    (|inv_17| |main::1::x|))))

(declare-fun |inv_15| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)))
  (=> (and 
    (|inv_17| |main::1::x_1|)
       (= (bvadd |main::1::x_1| (_ bv1 32)) |main::1::x|)) 
    (|inv_15| |main::1::x|))))

(declare-fun |inv_13| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_15| |main::1::x|)
       (not (= |main::1::x| (_ bv6 32)))) 
    (|inv_13| |main::1::x|))))

(declare-fun |inv_2| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_15| |main::1::x|)
       (= |main::1::x| (_ bv6 32))) 
    (|inv_2| |main::1::x|))))

(declare-fun |inv_6| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> 
    (|inv_13| |main::1::x|) 
    (|inv_6| |main::1::x|))))

(declare-fun |inv_10| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_6| |main::1::x|)
       (= |main::1::x| (_ bv999 32))) 
    (|inv_10| |main::1::x|))))

(declare-fun |inv_8| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_10| |main::1::x|)
       (not (bvsge |main::1::x| (_ bv2 32)))) 
    (|inv_8| |main::1::x|))))

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_10| |main::1::x|)
       (bvsge |main::1::x| (_ bv2 32))) 
    (|inv_3| |main::1::x|))))

(assert (forall ((|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)))
  (=> (and 
    (|inv_8| |main::1::x_1|)
       (= (bvadd |main::1::x_1| (_ bv2 32)) |main::1::x|)) 
    (|inv_6| |main::1::x|))))

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_6| |main::1::x|)
       (not (= |main::1::x| (_ bv999 32)))) 
    (|inv_3| |main::1::x|))))

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_3| |main::1::x|)
       (not true)) 
    (|inv_2| |main::1::x|))))

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_2| |main::1::x|)
       (not (= |main::1::x| (_ bv5 32)))) false)))

(declare-fun |inv_1| () Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_2| |main::1::x|)
       (= |main::1::x| (_ bv5 32))) 
    |inv_1|)))

(assert (=> 
    |inv_1| true))

(check-sat)