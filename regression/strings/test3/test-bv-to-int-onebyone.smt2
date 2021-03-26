(set-option :produce-models true)
(set-option :incremental true)
(set-logic ALL)

(declare-fun s () String)
(declare-fun s2 () String)
(declare-fun s3 () String)

(define-sort cprover.Pos () (_ BitVec 32))
(define-fun cprover.ubv_to_int ((?x cprover.Pos)) Int (let ((bit0 (_ bv0 1)))
 (+ (ite (= ((_ extract 0 0) ?x) bit0) 0 1) (ite (= ((_ extract 1 1) ?x) bit0) 0 2) (ite (= ((_ extract 2 2) ?x) bit0) 0 4) (ite (= ((_ extract 3 3) ?x) bit0) 0 8) (ite (= ((_ extract 4 4) ?x) bit0) 0 16) (ite (= ((_ extract 5 5) ?x) bit0) 0 32) (ite (= ((_ extract 6 6) ?x) bit0) 0 64) (ite (= ((_ extract 7 7) ?x) bit0) 0 128) (ite (= ((_ extract 8 8) ?x) bit0) 0 256) (ite (= ((_ extract 9 9) ?x) bit0) 0 512) (ite (= ((_ extract 10 10) ?x) bit0) 0 1024) (ite (= ((_ extract 11 11) ?x) bit0) 0 2048) (ite (= ((_ extract 12 12) ?x) bit0) 0 4096) (ite (= ((_ extract 13 13) ?x) bit0) 0 8192) (ite (= ((_ extract 14 14) ?x) bit0) 0 16384) (ite (= ((_ extract 15 15) ?x) bit0) 0 32768) (ite (= ((_ extract 16 16) ?x) bit0) 0 65536) (ite (= ((_ extract 17 17) ?x) bit0) 0 131072) (ite (= ((_ extract 18 18) ?x) bit0) 0 262144) (ite (= ((_ extract 19 19) ?x) bit0) 0 524288) (ite (= ((_ extract 20 20) ?x) bit0) 0 1048576) (ite (= ((_ extract 21 21) ?x) bit0) 0 2097152) (ite (= ((_ extract 22 22) ?x) bit0) 0 4194304) (ite (= ((_ extract 23 23) ?x) bit0) 0 8388608) (ite (= ((_ extract 24 24) ?x) bit0) 0 16777216) (ite (= ((_ extract 25 25) ?x) bit0) 0 33554432) (ite (= ((_ extract 26 26) ?x) bit0) 0 67108864) (ite (= ((_ extract 27 27) ?x) bit0) 0 134217728) (ite (= ((_ extract 28 28) ?x) bit0) 0 268435456) (ite (= ((_ extract 29 29) ?x) bit0) 0 536870912) (ite (= ((_ extract 30 30) ?x) bit0) 0 1073741824) (ite (= ((_ extract 31 31) ?x) bit0) 0 2147483648) 0)))

(declare-fun bvi () cprover.Pos)
(define-fun i () Int (cprover.ubv_to_int bvi))

(assert (= s (str.++ s2 s3)))

(assert (= (str.len s2) i))
(assert (= s3 "pippo"))

(define-fun p1 () Bool (= (str.len s) (+ i 5)))
(define-fun p2 () Bool (str.suffixof "po" s))
(define-fun p3 () Bool (= (str.at s i) "p"))

(push 1)
(assert (not p1))
(check-sat)
(pop 1)

(push 1)
(assert (not p2))
(check-sat)
(pop 1)

(push 1)
(assert (not p3))
(check-sat)
(pop 1)
