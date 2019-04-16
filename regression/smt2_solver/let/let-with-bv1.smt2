(set-logic QF_BV)

; try 'let' on bitvectors

(define-fun x () (_ BitVec 4) #x0)

; very simple
(define-fun let0 () Bool (= (let ((x #x0)) #x1) #x1))

; let hides the function 'x'
(define-fun let1 () Bool (= (let ((x #x1)) x) #x1))

; the binding isn't visible immediately
(define-fun let2 () Bool (= (let ((x x)) x) #x0))

; parallel let
(define-fun let3 () Bool (= (let ((x #x1) (y x)) y) #x0))

; limited scope
(define-fun let4 () Bool (and (= (let ((x #x1)) x) #x1) (= x #x0)))

; all must be true

(assert (not (and
  let0
  let1
  let2
  let3
  let4
  )))

(check-sat)
