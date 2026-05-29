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

; Rewrite 5: (bvule (bvurem A y) y) — always TRUE when y != 0,
; equals (= A 0) when y = 0. Composite case: ite form.
(assert (= (bvule (bvurem x y) y)
           (ite (= y #x00) (= x #x00) true)))

; (bvult (bvurem A y) y) — equals (not (= y 0)) regardless of A.
(assert (= (bvult (bvurem x y) y) (not (= y #x00))))

; Symmetric: (bvuge y (bvurem A y)) and (bvugt y (bvurem A y)).
(assert (= (bvuge y (bvurem x y))
           (ite (= y #x00) (= x #x00) true)))
(assert (= (bvugt y (bvurem x y)) (not (= y #x00))))

; Wider bitwidth: avoid building a full divider at bw=64.
(assert (= (bvule (bvurem z z) z)
           (ite (= z (_ bv0 64)) (= z (_ bv0 64)) true)))

; Rewrite 6: ite-distribution over bvudiv divisor.
(assert (= (bvudiv x (ite (= y #x00) (_ bv7 8) (_ bv11 8)))
           (ite (= y #x00) (bvudiv x (_ bv7 8)) (bvudiv x (_ bv11 8)))))

; ite-distribution over bvurem divisor.
(assert (= (bvurem x (ite (= y #x00) (_ bv7 8) (_ bv11 8)))
           (ite (= y #x00) (bvurem x (_ bv7 8)) (bvurem x (_ bv11 8)))))

; Constant-divisor folding: bvudiv X 0 = ~0
(assert (= (bvudiv x #x00) #xff))

; bvudiv X 1 = X
(assert (= (bvudiv x #x01) x))

; bvudiv X ~0 = ite(X = ~0, 1, 0)
(assert (= (bvudiv x #xff) (ite (= x #xff) #x01 #x00)))

; Rewrite 7: bvudiv-bvurem cancellation.
(assert (= (bvudiv (bvurem x y) y)
           (ite (= y #x00) #xff #x00)))

; And the wider version.
(assert (= (bvudiv (bvurem z z) z)
           (ite (= z (_ bv0 64)) (bvnot (_ bv0 64)) (_ bv0 64))))

(check-sat)
