; Test that let-bound arrays are properly connected to the original
; array in the array theory. A let binding creates a fresh symbol
; internally; without proper connection, the element-wise constraints
; on the original array don't propagate to the let-bound copy.
(set-option :produce-models true)
(declare-fun arr () (Array (_ BitVec 32) (_ BitVec 32)))
(assert (= (select arr (_ bv0 32)) (_ bv42 32)))
(assert (= (select arr (_ bv1 32)) (_ bv99 32)))
(assert (not (= (let ((?a arr)) (select ?a (_ bv1 32))) (_ bv99 32))))
(check-sat)
(exit)
