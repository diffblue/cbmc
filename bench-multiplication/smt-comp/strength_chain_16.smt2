; Verify a chain of strength reductions
(set-logic QF_BV)
(declare-fun x () (_ BitVec 16))
; x*15 == (x<<4) - x
(define-fun mul15a () (_ BitVec 16) (bvmul x (_ bv15 16)))
(define-fun mul15b () (_ BitVec 16) (bvsub (bvshl x (_ bv4 16)) x))
; x*17 == (x<<4) + x
(define-fun mul17a () (_ BitVec 16) (bvmul x (_ bv17 16)))
(define-fun mul17b () (_ BitVec 16) (bvadd (bvshl x (_ bv4 16)) x))
; x*255 == (x<<8) - x
(define-fun mul255a () (_ BitVec 16) (bvmul x (_ bv255 16)))
(define-fun mul255b () (_ BitVec 16) (bvsub (bvshl x (_ bv8 16)) x))
(assert (or (not (= mul15a mul15b)) (not (= mul17a mul17b)) (not (= mul255a mul255b))))
(check-sat)
(exit)
