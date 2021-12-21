; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)

(declare-fun |inv_11| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::1::k| (_ BitVec 32)) (|main::1::1::1::j| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> true 
    (|inv_11| |main::1::1::1::1::k| |main::1::1::1::j| |main::1::1::i| |main::1::x|))))

(declare-fun |inv_5| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::1::k| (_ BitVec 32)) (|main::1::1::1::1::k_1| (_ BitVec 32)) (|main::1::1::1::1::k_2| (_ BitVec 32)) (|main::1::1::1::j| (_ BitVec 32)) (|main::1::1::1::j_1| (_ BitVec 32)) (|main::1::1::1::j_2| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::1::i_1| (_ BitVec 32)) (|main::1::1::i_2| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::x_2| (_ BitVec 32)))
  (=> (and 
    (|inv_11| |main::1::1::1::1::k_2| |main::1::1::1::j_2| |main::1::1::i_2| |main::1::x_2|)
       (= |main::1::1::1::1::k_2| |main::1::1::1::1::k_1|)
       (= |main::1::1::1::j_2| |main::1::1::1::j_1|)
       (= |main::1::1::i_2| |main::1::1::i_1|)
       (= (_ bv0 32) |main::1::x_1|)
       (= |main::1::1::1::1::k_1| |main::1::1::1::1::k|)
       (= |main::1::1::1::j_1| |main::1::1::1::j|)
       (= (_ bv0 32) |main::1::1::i|)
       (= |main::1::x_1| |main::1::x|)) 
    (|inv_5| |main::1::1::1::1::k| |main::1::1::1::j| |main::1::1::i| |main::1::x|))))

(declare-fun |inv_10| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::1::k| (_ BitVec 32)) (|main::1::1::1::j| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_5| |main::1::1::1::1::k| |main::1::1::1::j| |main::1::1::i| |main::1::x|)
       (not (bvsge |main::1::1::i| (_ bv3 32)))) 
    (|inv_10| |main::1::1::1::1::k| |main::1::1::1::j| |main::1::1::i| |main::1::x|))))

(declare-fun |inv_6| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::1::k| (_ BitVec 32)) (|main::1::1::1::1::k_1| (_ BitVec 32)) (|main::1::1::1::j| (_ BitVec 32)) (|main::1::1::1::j_1| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::1::i_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)))
  (=> (and 
    (|inv_10| |main::1::1::1::1::k_1| |main::1::1::1::j_1| |main::1::1::i_1| |main::1::x_1|)
       (= |main::1::1::1::1::k_1| |main::1::1::1::1::k|)
       (= (_ bv0 32) |main::1::1::1::j|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= |main::1::x_1| |main::1::x|)) 
    (|inv_6| |main::1::1::1::1::k| |main::1::1::1::j| |main::1::1::i| |main::1::x|))))

(declare-fun |inv_9| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::1::k| (_ BitVec 32)) (|main::1::1::1::j| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_6| |main::1::1::1::1::k| |main::1::1::1::j| |main::1::1::i| |main::1::x|)
       (not (bvsge |main::1::1::1::j| (_ bv3 32)))) 
    (|inv_9| |main::1::1::1::1::k| |main::1::1::1::j| |main::1::1::i| |main::1::x|))))

(declare-fun |inv_7| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::1::k| (_ BitVec 32)) (|main::1::1::1::1::k_1| (_ BitVec 32)) (|main::1::1::1::j| (_ BitVec 32)) (|main::1::1::1::j_1| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::1::i_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)))
  (=> (and 
    (|inv_9| |main::1::1::1::1::k_1| |main::1::1::1::j_1| |main::1::1::i_1| |main::1::x_1|)
       (= (_ bv0 32) |main::1::1::1::1::k|)
       (= |main::1::1::1::j_1| |main::1::1::1::j|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= |main::1::x_1| |main::1::x|)) 
    (|inv_7| |main::1::1::1::1::k| |main::1::1::1::j| |main::1::1::i| |main::1::x|))))

(declare-fun |inv_8| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::1::k| (_ BitVec 32)) (|main::1::1::1::j| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_7| |main::1::1::1::1::k| |main::1::1::1::j| |main::1::1::i| |main::1::x|)
       (not (bvsge |main::1::1::1::1::k| (_ bv3 32)))) 
    (|inv_8| |main::1::1::1::1::k| |main::1::1::1::j| |main::1::1::i| |main::1::x|))))

(assert (forall ((|main::1::1::1::1::k| (_ BitVec 32)) (|main::1::1::1::1::k_1| (_ BitVec 32)) (|main::1::1::1::1::k_2| (_ BitVec 32)) (|main::1::1::1::j| (_ BitVec 32)) (|main::1::1::1::j_1| (_ BitVec 32)) (|main::1::1::1::j_2| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::1::i_1| (_ BitVec 32)) (|main::1::1::i_2| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)) (|main::1::x_2| (_ BitVec 32)))
  (=> (and 
    (|inv_8| |main::1::1::1::1::k_2| |main::1::1::1::j_2| |main::1::1::i_2| |main::1::x_2|)
       (= |main::1::1::1::1::k_2| |main::1::1::1::1::k_1|)
       (= |main::1::1::1::j_2| |main::1::1::1::j_1|)
       (= |main::1::1::i_2| |main::1::1::i_1|)
       (= (bvadd |main::1::x_2| (_ bv1 32)) |main::1::x_1|)
       (= (bvadd |main::1::1::1::1::k_1| (_ bv1 32)) |main::1::1::1::1::k|)
       (= |main::1::1::1::j_1| |main::1::1::1::j|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= |main::1::x_1| |main::1::x|)) 
    (|inv_7| |main::1::1::1::1::k| |main::1::1::1::j| |main::1::1::i| |main::1::x|))))

(assert (forall ((|main::1::1::1::1::k| (_ BitVec 32)) (|main::1::1::1::1::k_1| (_ BitVec 32)) (|main::1::1::1::j| (_ BitVec 32)) (|main::1::1::1::j_1| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::1::i_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)))
  (=> (and 
    (|inv_7| |main::1::1::1::1::k_1| |main::1::1::1::j_1| |main::1::1::i_1| |main::1::x_1|)
       (not (not (bvsge |main::1::1::1::1::k_1| (_ bv3 32))))
       (= |main::1::1::1::1::k_1| |main::1::1::1::1::k|)
       (= (bvadd |main::1::1::1::j_1| (_ bv1 32)) |main::1::1::1::j|)
       (= |main::1::1::i_1| |main::1::1::i|)
       (= |main::1::x_1| |main::1::x|)) 
    (|inv_6| |main::1::1::1::1::k| |main::1::1::1::j| |main::1::1::i| |main::1::x|))))

(assert (forall ((|main::1::1::1::1::k| (_ BitVec 32)) (|main::1::1::1::1::k_1| (_ BitVec 32)) (|main::1::1::1::j| (_ BitVec 32)) (|main::1::1::1::j_1| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::1::i_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)))
  (=> (and 
    (|inv_6| |main::1::1::1::1::k_1| |main::1::1::1::j_1| |main::1::1::i_1| |main::1::x_1|)
       (not (not (bvsge |main::1::1::1::j_1| (_ bv3 32))))
       (= |main::1::1::1::1::k_1| |main::1::1::1::1::k|)
       (= |main::1::1::1::j_1| |main::1::1::1::j|)
       (= (bvadd |main::1::1::i_1| (_ bv1 32)) |main::1::1::i|)
       (= |main::1::x_1| |main::1::x|)) 
    (|inv_5| |main::1::1::1::1::k| |main::1::1::1::j| |main::1::1::i| |main::1::x|))))

(declare-fun |inv_4| ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::1::k| (_ BitVec 32)) (|main::1::1::1::j| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> 
    (|inv_5| |main::1::1::1::1::k| |main::1::1::1::j| |main::1::1::i| |main::1::x|) 
    (|inv_4| |main::1::1::1::1::k| |main::1::1::1::j| |main::1::1::i| |main::1::x|))))

(declare-fun |inv_3| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::1::1::k| (_ BitVec 32)) (|main::1::1::1::j| (_ BitVec 32)) (|main::1::1::i| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> 
    (|inv_4| |main::1::1::1::1::k| |main::1::1::1::j| |main::1::1::i| |main::1::x|) 
    (|inv_3| |main::1::1::i| |main::1::x|))))

(declare-fun |inv_2| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::i| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_3| |main::1::1::i| |main::1::x|)
       (not (not (bvsge |main::1::1::i| (_ bv3 32))))) 
    (|inv_2| |main::1::x|))))

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_2| |main::1::x|)
       (not (bvsgt |main::1::x| (_ bv27 32)))) false)))

(declare-fun |inv_1| () Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_2| |main::1::x|)
       (bvsgt |main::1::x| (_ bv27 32))) 
    |inv_1|)))

(assert (=> 
    |inv_1| true))

(check-sat)