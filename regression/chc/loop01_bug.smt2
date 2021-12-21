; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)

(declare-fun |inv_5| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::i| (_ BitVec 32)))
  (=> true 
    (|inv_5| |main::1::1::i|))))

(declare-fun |inv_3| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::i| (_ BitVec 32)) (|main::1::1::i_1| (_ BitVec 32)))
  (=> (and 
    (|inv_5| |main::1::1::i_1|)
       (= (_ bv0 32) |main::1::1::i|)) 
    (|inv_3| |main::1::1::i|))))

(declare-fun |inv_4| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::i| (_ BitVec 32)))
  (=> (and 
    (|inv_3| |main::1::1::i|)
       (not (bvsge |main::1::1::i| (_ bv10 32)))) 
    (|inv_4| |main::1::1::i|))))

(assert (forall ((|main::1::1::i| (_ BitVec 32)) (|main::1::1::i_1| (_ BitVec 32)) (|main::1::1::i_2| (_ BitVec 32)))
  (=> (and 
    (|inv_4| |main::1::1::i_2|)
       (= (bvadd |main::1::1::i_2| (_ bv1 32)) |main::1::1::i_1|)
       (= (bvadd |main::1::1::i_1| (_ bv1 32)) |main::1::1::i|)) 
    (|inv_3| |main::1::1::i|))))

(declare-fun |inv_2| () Bool)

(assert (forall ((|main::1::1::i| (_ BitVec 32)))
  (=> (and 
    (|inv_3| |main::1::1::i|)
       (not (not (bvsge |main::1::1::i| (_ bv10 32))))) 
    |inv_2|)))

(assert (=> (and 
    |inv_2|
       (not false)) false))

(declare-fun |inv_1| () Bool)

(assert (=> (and 
    |inv_2|
       false) 
    |inv_1|))

(assert (=> 
    |inv_1| true))

(check-sat)