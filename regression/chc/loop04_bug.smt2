; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)

(declare-fun |inv_18| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::z| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::b| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> true 
    (|inv_18| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|))))

(declare-fun |inv_6| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::z| (_ BitVec 32)) (|main::1::1::1::z_1| (_ BitVec 32)) (|main::1::1::1::z_2| (_ BitVec 32)) (|main::1::1::1::z_3| (_ BitVec 32)) (|main::1::1::1::z_4| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::1::i_1| (_ BitVec 32)) (|main::1::1::i_2| (_ BitVec 32)) (|main::1::1::i_3| (_ BitVec 32)) (|main::1::1::i_4| (_ BitVec 32)) (|main::1::b| (_ BitVec 32)) (|main::1::b_1| (_ BitVec 32)) (|main::1::b_2| (_ BitVec 32)) (|main::1::b_3| (_ BitVec 32)) (|main::1::b_4| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::x_2| (_ BitVec 32)) (|main::1::x_3| (_ BitVec 32)) (|main::1::x_4| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)) (|main::1::y_1| (_ BitVec 32)) (|main::1::y_2| (_ BitVec 32)) (|main::1::y_3| (_ BitVec 32)) (|main::1::y_4| (_ BitVec 32)))
  (=> (and 
    (|inv_18| |main::1::1::1::z_4| |main::1::1::i_4| |main::1::b_4| |main::1::x_4| |main::1::y_4|)
       (= |main::1::1::1::z_4| |main::1::1::1::z_3|)
       (= |main::1::1::i_4| |main::1::1::i_3|)
       (= |main::1::b_4| |main::1::b_3|)
       (= (_ bv0 32) |main::1::x_3|)
       (= |main::1::y_4| |main::1::y_3|)
       (= |main::1::1::1::z_3| |main::1::1::1::z_2|)
       (= |main::1::1::i_3| |main::1::1::i_2|)
       (= |main::1::b_3| |main::1::b_2|)
       (= |main::1::x_3| |main::1::x_2|)
       (= (_ bv5 32) |main::1::y_2|)
       (= |main::1::1::1::z_2| |main::1::1::1::z_1|)
       (= |main::1::1::i_2| |main::1::1::i_1|)
       (= (_ bv0 32) |main::1::b_1|)
       (= |main::1::x_2| |main::1::x_1|)
       (= |main::1::y_2| |main::1::y_1|)
       (= |main::1::1::1::z_1| |main::1::1::1::z|)
       (= (_ bv0 32) |main::1::1::i|)
       (= |main::1::b_1| |main::1::b|)
       (= |main::1::x_1| |main::1::x|)
       (= |main::1::y_1| |main::1::y|)) 
    (|inv_6| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|))))

(declare-fun |inv_17| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::z| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::b| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_6| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|)
       (not (bvsge |main::1::1::i| (_ bv10 32)))) 
    (|inv_17| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|))))

(declare-fun |inv_15| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::z| (_ BitVec 32)) (|main::1::1::1::z_1| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::1::i_1| (_ BitVec 32)) (|main::1::b| (_ BitVec 32)) (|main::1::b_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)) (|main::1::y_1| (_ BitVec 32)))
  (=> (and 
    (|inv_17| |main::1::1::1::z_1| |main::1::1::i_1| |main::1::b_1| |main::1::x_1| |main::1::y_1|)
       (= |main::1::x_1| |main::1::1::1::z|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= |main::1::b_1| |main::1::b|)
       (= |main::1::x_1| |main::1::x|)
       (= |main::1::y_1| |main::1::y|)) 
    (|inv_15| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|))))

(declare-fun |inv_13| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::z| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::b| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_15| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|)
       (not (= |main::1::1::1::z| (_ bv4 32)))) 
    (|inv_13| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|))))

(declare-fun |inv_14| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::z| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::b| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_15| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|)
       (= |main::1::1::1::z| (_ bv4 32))) 
    (|inv_14| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|))))

(assert (forall ((|main::1::1::1::z| (_ BitVec 32)) (|main::1::1::1::z_1| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::1::i_1| (_ BitVec 32)) (|main::1::b| (_ BitVec 32)) (|main::1::b_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)) (|main::1::y_1| (_ BitVec 32)))
  (=> (and 
    (|inv_14| |main::1::1::1::z_1| |main::1::1::i_1| |main::1::b_1| |main::1::x_1| |main::1::y_1|)
       (= |main::1::1::1::z_1| |main::1::1::1::z|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= (_ bv1 32) |main::1::b|)
       (= |main::1::x_1| |main::1::x|)
       (= |main::1::y_1| |main::1::y|)) 
    (|inv_13| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|))))

(declare-fun |inv_11| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::z| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::b| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> 
    (|inv_13| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|) 
    (|inv_11| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|))))

(declare-fun |inv_9| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::z| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::b| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_11| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|)
       (not (not (= |main::1::b| (_ bv0 32))))) 
    (|inv_9| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|))))

(declare-fun |inv_10| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::z| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::b| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_11| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|)
       (not (= |main::1::b| (_ bv0 32)))) 
    (|inv_10| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|))))

(assert (forall ((|main::1::1::1::z| (_ BitVec 32)) (|main::1::1::1::z_1| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::1::i_1| (_ BitVec 32)) (|main::1::b| (_ BitVec 32)) (|main::1::b_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)) (|main::1::y_1| (_ BitVec 32)))
  (=> (and 
    (|inv_10| |main::1::1::1::z_1| |main::1::1::i_1| |main::1::b_1| |main::1::x_1| |main::1::y_1|)
       (= |main::1::1::1::z_1| |main::1::1::1::z|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= |main::1::b_1| |main::1::b|)
       (= |main::1::x_1| |main::1::x|)
       (= (bvsub |main::1::y_1| (_ bv1 32)) |main::1::y|)) 
    (|inv_9| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|))))

(assert (forall ((|main::1::1::1::z| (_ BitVec 32)) (|main::1::1::1::z_1| (_ BitVec 32)) (|main::1::1::1::z_2| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::1::i_1| (_ BitVec 32)) (|main::1::1::i_2| (_ BitVec 32)) (|main::1::b| (_ BitVec 32)) (|main::1::b_1| (_ BitVec 32)) (|main::1::b_2| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::x_2| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)) (|main::1::y_1| (_ BitVec 32)) (|main::1::y_2| (_ BitVec 32)))
  (=> (and 
    (|inv_9| |main::1::1::1::z_2| |main::1::1::i_2| |main::1::b_2| |main::1::x_2| |main::1::y_2|)
       (= |main::1::1::1::z_2| |main::1::1::1::z_1|)
       (= |main::1::1::i_2| |main::1::1::i_1|)
       (= |main::1::b_2| |main::1::b_1|)
       (= (bvadd |main::1::x_2| (_ bv1 32)) |main::1::x_1|)
       (= |main::1::y_2| |main::1::y_1|)
       (= |main::1::1::1::z_1| |main::1::1::1::z|)
       (= (bvadd |main::1::1::i_1| (_ bv1 32)) |main::1::1::i|)
       (= |main::1::b_1| |main::1::b|)
       (= |main::1::x_1| |main::1::x|)
       (= |main::1::y_1| |main::1::y|)) 
    (|inv_6| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|))))

(declare-fun |inv_3| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::z| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::b| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> 
    (|inv_6| |main::1::1::1::z| |main::1::1::i| |main::1::b| |main::1::x| |main::1::y|) 
    (|inv_3| |main::1::1::i| |main::1::y|))))

(declare-fun |inv_2| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::i| (_ BitVec 32)) (|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_3| |main::1::1::i| |main::1::y|)
       (not (not (bvsge |main::1::1::i| (_ bv10 32))))) 
    (|inv_2| |main::1::y|))))

(assert (forall ((|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_2| |main::1::y|)
       (not (= |main::1::y| (_ bv0 32)))) false)))

(declare-fun |inv_1| () Bool)

(assert (forall ((|main::1::y| (_ BitVec 32)))
  (=> (and 
    (|inv_2| |main::1::y|)
       (= |main::1::y| (_ bv0 32))) 
    |inv_1|)))

(assert (=> 
    |inv_1| true))

(check-sat)