; SMT 2
; Generated for Z3
(set-info :source "Generated by CBMC 5.4")
(set-option :produce-models true)
; string support via PASS-style quantified arrays
(define-sort cprover.Char () (_ BitVec 8))
(define-sort cprover.Pos () (_ BitVec 32))
(define-sort cprover.String () (Array cprover.Pos cprover.Char))
(declare-fun cprover.str.len (cprover.String) cprover.Pos)

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$7!0@1#2| () Bool)
; convert
(define-fun |B0| () Bool |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$7!0@1#2|)

; set_to true (equal)
(define-fun |__CPROVER_dead_object#1| () (_ BitVec 32) (_ bv0 32))

; set_to true (equal)
(define-fun |__CPROVER_deallocated#1| () (_ BitVec 32) (_ bv0 32))

; set_to true (equal)
(define-fun |__CPROVER_malloc_is_new_array#1| () Bool false)

; set_to true (equal)
(define-fun |__CPROVER_malloc_object#1| () (_ BitVec 32) (_ bv0 32))

; set_to true (equal)
(define-fun |__CPROVER_malloc_size#1| () (_ BitVec 32) (_ bv0 32))

; set_to true (equal)
(define-fun |__CPROVER_memory_leak#1| () (_ BitVec 32) (_ bv0 32))

; set_to true (equal)
(define-fun |__CPROVER_next_thread_id#1| () (_ BitVec 32) (_ bv0 32))

; set_to true (equal)
(define-fun |__CPROVER_pipe_count#1| () (_ BitVec 32) (_ bv0 32))

; set_to true (equal)
(define-fun |__CPROVER_rounding_mode!0#1| () (_ BitVec 32) (_ bv0 32))

; set_to true (equal)
(define-fun |__CPROVER_thread_id!0#1| () (_ BitVec 32) (_ bv0 32))

; the following is a substitute for lambda i. x
(declare-fun array_of.0 () (Array (_ BitVec 32) Bool))
; set_to true (equal)
(define-fun |__CPROVER_threads_exited#1| () (Array (_ BitVec 32) Bool) array_of.0)

(declare-fun string.1 () cprover.String)
(assert (= (select string.1 (_ bv0 32)) (_ bv97 8)))
(assert (= (select string.1 (_ bv1 32)) (_ bv98 8)))
(assert (= (select string.1 (_ bv2 32)) (_ bv99 8)))
(assert (= (cprover.str.len string.1) (_ bv3 32)))
; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#2| () cprover.String string.1)

; find_symbols
(declare-fun |main::1::x2!0@1#1| () cprover.String)
; string concatenation
(declare-fun string_concat.2 () cprover.String)
(define-fun string_concat.s0.2 () cprover.String |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#2|)
(define-fun string_concat.s1.2 () cprover.String |main::1::x2!0@1#1|)
(assert (forall ((?n cprover.Pos)) (=> (bvult ?n (cprover.str.len string_concat.s0.2)) (= (select string_concat.s0.2 ?n) (select string_concat.2 ?n)))))
(assert (forall ((?n cprover.Pos)) (=> (bvult ?n (cprover.str.len string_concat.s1.2)) (= (select string_concat.s1.2 ?n) (select string_concat.2 (bvadd (cprover.str.len string_concat.s0.2) ?n))))))
(assert (= (cprover.str.len string_concat.2) (bvadd (cprover.str.len string_concat.s0.2) (cprover.str.len string_concat.s1.2))))
(assert (bvuge (cprover.str.len string_concat.2) (cprover.str.len string_concat.s0.2)))
(assert (bvuge (cprover.str.len string_concat.2) (cprover.str.len string_concat.s1.2)))

; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$2!0@1#2| () cprover.String string_concat.2)

; find_symbols
(declare-fun |main::1::x1!0@1#1| () cprover.String)
; string concatenation
(declare-fun string_concat.3 () cprover.String)
(define-fun string_concat.s0.3 () cprover.String |main::1::x1!0@1#1|)
(define-fun string_concat.s1.3 () cprover.String |main::$tmp::return_value___CPROVER_uninterpreted_strcat$2!0@1#2|)
(assert (forall ((?n cprover.Pos)) (=> (bvult ?n (cprover.str.len string_concat.s0.3)) (= (select string_concat.s0.3 ?n) (select string_concat.3 ?n)))))
(assert (forall ((?n cprover.Pos)) (=> (bvult ?n (cprover.str.len string_concat.s1.3)) (= (select string_concat.s1.3 ?n) (select string_concat.3 (bvadd (cprover.str.len string_concat.s0.3) ?n))))))
(assert (= (cprover.str.len string_concat.3) (bvadd (cprover.str.len string_concat.s0.3) (cprover.str.len string_concat.s1.3))))
(assert (bvuge (cprover.str.len string_concat.3) (cprover.str.len string_concat.s0.3)))
(assert (bvuge (cprover.str.len string_concat.3) (cprover.str.len string_concat.s1.3)))

; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$3!0@1#2| () cprover.String string_concat.3)

(declare-fun string.4 () cprover.String)
(assert (= (select string.4 (_ bv0 32)) (_ bv101 8)))
(assert (= (select string.4 (_ bv1 32)) (_ bv102 8)))
(assert (= (cprover.str.len string.4) (_ bv2 32)))
; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$4!0@1#2| () cprover.String string.4)

; find_symbols
(declare-fun |main::1::y2!0@1#1| () cprover.String)
; string concatenation
(declare-fun string_concat.5 () cprover.String)
(define-fun string_concat.s0.5 () cprover.String |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$4!0@1#2|)
(define-fun string_concat.s1.5 () cprover.String |main::1::y2!0@1#1|)
(assert (forall ((?n cprover.Pos)) (=> (bvult ?n (cprover.str.len string_concat.s0.5)) (= (select string_concat.s0.5 ?n) (select string_concat.5 ?n)))))
(assert (forall ((?n cprover.Pos)) (=> (bvult ?n (cprover.str.len string_concat.s1.5)) (= (select string_concat.s1.5 ?n) (select string_concat.5 (bvadd (cprover.str.len string_concat.s0.5) ?n))))))
(assert (= (cprover.str.len string_concat.5) (bvadd (cprover.str.len string_concat.s0.5) (cprover.str.len string_concat.s1.5))))
(assert (bvuge (cprover.str.len string_concat.5) (cprover.str.len string_concat.s0.5)))
(assert (bvuge (cprover.str.len string_concat.5) (cprover.str.len string_concat.s1.5)))

; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$5!0@1#2| () cprover.String string_concat.5)

; find_symbols
(declare-fun |main::1::y1!0@1#1| () cprover.String)
; string concatenation
(declare-fun string_concat.6 () cprover.String)
(define-fun string_concat.s0.6 () cprover.String |main::1::y1!0@1#1|)
(define-fun string_concat.s1.6 () cprover.String |main::$tmp::return_value___CPROVER_uninterpreted_strcat$5!0@1#2|)
(assert (forall ((?n cprover.Pos)) (=> (bvult ?n (cprover.str.len string_concat.s0.6)) (= (select string_concat.s0.6 ?n) (select string_concat.6 ?n)))))
(assert (forall ((?n cprover.Pos)) (=> (bvult ?n (cprover.str.len string_concat.s1.6)) (= (select string_concat.s1.6 ?n) (select string_concat.6 (bvadd (cprover.str.len string_concat.s0.6) ?n))))))
(assert (= (cprover.str.len string_concat.6) (bvadd (cprover.str.len string_concat.s0.6) (cprover.str.len string_concat.s1.6))))
(assert (bvuge (cprover.str.len string_concat.6) (cprover.str.len string_concat.s0.6)))
(assert (bvuge (cprover.str.len string_concat.6) (cprover.str.len string_concat.s1.6)))

; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$6!0@1#2| () cprover.String string_concat.6)

; string equal
(declare-fun string_equal.7 () Bool)
(define-fun string_equal.s1.7 () cprover.String |main::$tmp::return_value___CPROVER_uninterpreted_strcat$3!0@1#2|)
(define-fun string_equal.s2.7 () cprover.String |main::$tmp::return_value___CPROVER_uninterpreted_strcat$6!0@1#2|)
(declare-fun string_equal.idx.7 () cprover.Pos)
(assert (=> string_equal.7 (= (cprover.str.len string_equal.s1.7) (cprover.str.len string_equal.s2.7))))
(assert (forall ((?n cprover.Pos)) (=> (and string_equal.7 (bvult ?n (cprover.str.len string_equal.s1.7))) (= (select string_equal.s1.7 ?n) (select string_equal.s2.7 ?n)))))
(assert (=> (not string_equal.7) (or (not (= (cprover.str.len string_equal.s1.7) (cprover.str.len string_equal.s2.7)))
(and (bvult string_equal.idx.7 (cprover.str.len string_equal.s1.7)) (not (= (select string_equal.s1.7 string_equal.idx.7) (select string_equal.s2.7 string_equal.idx.7)))))))

; set_to true
(assert (= |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$7!0@1#2| string_equal.7))

; convert
(define-fun |B1| () Bool (= |main::1::x1!0@1#1| |main::1::x1!0@1#1|))

; convert
(define-fun |B2| () Bool (= |main::1::x2!0@1#1| |main::1::x2!0@1#1|))

; convert
(define-fun |B3| () Bool (= |main::1::y1!0@1#1| |main::1::y1!0@1#1|))

; convert
(define-fun |B4| () Bool (= |main::1::y2!0@1#1| |main::1::y2!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#1| () cprover.String)
; convert
(define-fun |B5| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$2!0@1#1| () cprover.String)
; convert
(define-fun |B6| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_strcat$2!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_strcat$2!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$3!0@1#1| () cprover.String)
; convert
(define-fun |B7| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_strcat$3!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_strcat$3!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$4!0@1#1| () cprover.String)
; convert
(define-fun |B8| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$4!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$4!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$5!0@1#1| () cprover.String)
; convert
(define-fun |B9| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_strcat$5!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_strcat$5!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$6!0@1#1| () cprover.String)
; convert
(define-fun |B10| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_strcat$6!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_strcat$6!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$7!0@1#1| () Bool)
; convert
(define-fun |B11| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$7!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$7!0@1#1|))

; set_to true
(assert |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$7!0@1#2|)

; convert
(define-fun |B12| () Bool (not |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$7!0@1#2|))

(check-sat)

(get-value (|B0|))
(get-value (|B1|))
(get-value (|B10|))
(get-value (|B11|))
(get-value (|B12|))
(get-value (|B2|))
(get-value (|B3|))
(get-value (|B4|))
(get-value (|B5|))
(get-value (|B6|))
(get-value (|B7|))
(get-value (|B8|))
(get-value (|B9|))
(get-value (|__CPROVER_dead_object#1|))
(get-value (|__CPROVER_deallocated#1|))
(get-value (|__CPROVER_malloc_is_new_array#1|))
(get-value (|__CPROVER_malloc_object#1|))
(get-value (|__CPROVER_malloc_size#1|))
(get-value (|__CPROVER_memory_leak#1|))
(get-value (|__CPROVER_next_thread_id#1|))
(get-value (|__CPROVER_pipe_count#1|))
(get-value (|__CPROVER_rounding_mode!0#1|))
(get-value (|__CPROVER_thread_id!0#1|))
(get-value (|__CPROVER_threads_exited#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$2!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$2!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$3!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$3!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$5!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$5!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$6!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$6!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_equal$7!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_equal$7!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_literal$4!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_literal$4!0@1#2|))
(get-value (|main::1::x1!0@1#1|))
(get-value (|main::1::x2!0@1#1|))
(get-value (|main::1::y1!0@1#1|))
(get-value (|main::1::y2!0@1#1|))

(exit)
; end of SMT2 file
