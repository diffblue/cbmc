(set-logic QF_BV)

; From https://rise4fun.com/z3/tutorialcontent/guide

; Basic Bitvector Arithmetic
(define-fun b01 () Bool (= (bvadd #x07 #x03) #x0a)) ; addition
(define-fun b02 () Bool (= (bvsub #x07 #x03) #x04)) ; subtraction
(define-fun b03 () Bool (= (bvneg #x07) #xf9)) ; unary minus
(define-fun b04 () Bool (= (bvmul #x07 #x03) #x15)) ; multiplication
(define-fun b05 () Bool (= (bvurem #x07 #x03) #x01)) ; unsigned remainder
(define-fun b06 () Bool (= (bvsrem #x07 #x03) #x01)) ; signed remainder
(define-fun b07 () Bool (= (bvsmod #x07 #x03) #x01)) ; signed modulo
(define-fun b08 () Bool (= (bvshl #x07 #x03) #x38)) ; shift left
(define-fun b09 () Bool (= (bvlshr #xf0 #x03) #x1e)) ; unsigned (logical) shift right
(define-fun b10 () Bool (= (bvashr #xf0 #x03) #xfe)) ; signed (arithmetical) shift right#x0a

; rotation
(define-fun b11 () Bool (= ((_ rotate_left 2) #xf7) #xdf)) ; rotation left
(define-fun b12 () Bool (= ((_ rotate_right 2) #x07) #xc1)) ; rotation right

; Bitwise Operations

(define-fun w1 () Bool (= (bvor #x6 #x3) #x7))   ; bitwise or
(define-fun w2 () Bool (= (bvand #x6 #x3) #x2))  ; bitwise and
(define-fun w3 () Bool (= (bvnot #x6) #x9)) ; bitwise not
(define-fun w4 () Bool (= (bvnand #x6 #x3) #xd)) ; bitwise nand
(define-fun w5 () Bool (= (bvnor #x6 #x3) #x8)) ; bitwise nor
(define-fun w6 () Bool (= (bvxnor #x6 #x3) #xa)) ; bitwise xnor

; We can prove a bitwise version of deMorgan's law

(declare-const x (_ BitVec 64)) ; nullary function
(declare-var y (_ BitVec 64)) ; alternative syntax for declare-const
(define-fun d01 () Bool (= (bvand (bvnot x) (bvnot y)) (bvnot (bvor x y))))

; There is a fast way to check that fixed size numbers are powers of two

(define-fun is-power-of-two ((x (_ BitVec 4))) Bool 
  (= #x0 (bvand x (bvsub x #x1))))
(declare-const a (_ BitVec 4))
(define-fun power-test () Bool
  (= (is-power-of-two a) 
         (or (= a #x0) 
             (= a #x1) 
             (= a #x2) 
             (= a #x4) 
             (= a #x8))))

; Predicates over Bitvectors

(define-fun p1 () Bool (= (bvule #x0a #xf0) true))  ; unsigned less or equal
(define-fun p2 () Bool (= (bvult #x0a #xf0) true))  ; unsigned less than
(define-fun p3 () Bool (= (bvuge #x0a #xf0) false))  ; unsigned greater or equal
(define-fun p4 () Bool (= (bvugt #x0a #xf0) false))  ; unsigned greater than
(define-fun p5 () Bool (= (bvsle #x0a #xf0) false))  ; signed less or equal
(define-fun p6 () Bool (= (bvslt #x0a #xf0) false))  ; signed less than
(define-fun p7 () Bool (= (bvsge #x0a #xf0) true))  ; signed greater or equal
(define-fun p8 () Bool (= (bvsgt #x0a #xf0) true))  ; signed greater than

; all must be true

(assert (not (and
  b01 b02 b03 b04 b05 b06 b07 b08 b09 b10 b11 b12
  d01
  power-test
  p1 p2 p3 p4 p5 p6 p7 p8)))

(check-sat)
