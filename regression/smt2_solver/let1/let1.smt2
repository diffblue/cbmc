(set-logic QF_BV)

(define-fun x () Bool false)

; very simple
(define-fun let0 () Bool (let ((x false)) true))

; let hides the function 'x'
(define-fun let1 () Bool (let ((x true)) x))

; the binding isn't visible immediately
(define-fun let2 () Bool (not (let ((x x)) x)))

; parallel let
(define-fun let3 () Bool (let ((x true) (y x)) (not y)))

; limited scope
(define-fun let4 () Bool (and (let ((x true)) x) (not x)))

; all must be true

(assert (not (and
  let0
  let1
  let2
  let3
  let4
  )))

(check-sat)
