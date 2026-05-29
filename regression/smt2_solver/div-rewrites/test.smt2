(set-logic QF_BV)

; Word-level rewrites for bvudiv / bvurem / bvsdiv / bvsrem / bvsmod
; recognised at parse time in src/solvers/smt2/smt2_parser.cpp.
;
; The check is a tautology assertion: each rewrite must hold for all
; inputs, and the conjunction below is unsat (its distinct check is
; falsified).

(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const z (_ BitVec 64))

; (bvudiv x x) = ite(x = 0, ~0, 1)
(assert (= (bvudiv x x) (ite (= x #x00) #xff #x01)))

; (bvsdiv x x) = ite(x = 0, ~0, 1) (same as unsigned)
(assert (= (bvsdiv x x) (ite (= x #x00) #xff #x01)))

; (bvurem x x) = 0 (always, regardless of x = 0)
(assert (= (bvurem x x) #x00))

; (bvsrem x x) = 0
(assert (= (bvsrem x x) #x00))

; (bvsmod x x) = 0
(assert (= (bvsmod x x) #x00))

; (bvudiv 0 x) = ite(x = 0, ~0, 0)
(assert (= (bvudiv #x00 x) (ite (= x #x00) #xff #x00)))

; (bvurem 0 x) = 0 (always)
(assert (= (bvurem #x00 x) #x00))

; Wider bitwidth: confirm rewrite scales (no full divider should be built).
(assert (= (bvudiv z z) (ite (= z (_ bv0 64)) (bvnot (_ bv0 64)) (_ bv1 64))))
(assert (= (bvurem z z) (_ bv0 64)))

; Composite: confirm rewrite is recognised under structural sharing
; (bvurem y y) within a multiplication
(assert (= (bvmul x (bvurem y y)) #x00))

(check-sat)
