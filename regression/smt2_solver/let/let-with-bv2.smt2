(set-logic QF_BV)

(define-fun x () (_ BitVec 8) #x12)

; let hides the function 'x'
(define-fun let1 () Bool (let ((x #x4567)) (= x #x4567)))

; the binding isn't visible immediately
(define-fun let2 () Bool (= (let ((x x)) x) #x12))

; parallel let
(define-fun let3 () Bool (= (let ((x #x45) (y x)) y) #x12))

; limited scope
(define-fun let4 () Bool (and (let ((x true)) x) (= x #x12)))

; all must be true

(assert (not (and
  let1
  let2
  let3
  let4
  )))

(check-sat)
