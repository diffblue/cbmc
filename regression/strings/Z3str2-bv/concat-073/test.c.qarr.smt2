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
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#2| () Bool)
; convert
(define-fun |B0| () Bool |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#2|)

; convert
(define-fun |B1| () Bool |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#2|)

; convert
(define-fun |B2| () Bool |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#2|)

; convert
(define-fun |B3| () Bool |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#2|)

; convert
(define-fun |B4| () Bool |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#2|)

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$5!0@1#2| () Bool)
; convert
(define-fun |B5| () Bool (and |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#2| |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$5!0@1#2|))

; convert
(define-fun |B6| () Bool (and |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#2| |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$5!0@1#2|))

; convert
(define-fun |B7| () Bool (and |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#2| |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$5!0@1#2|))

; convert
(define-fun |B8| () Bool (and |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#2| |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$5!0@1#2|))

; convert
(define-fun |B9| () Bool (and |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#2| |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$5!0@1#2|))

; convert
(define-fun |B10| () Bool (and |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#2| |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$5!0@1#2|))

; convert
(define-fun |B11| () Bool (and |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#2| |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$5!0@1#2|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$3!0@1#2| () Bool)
; convert
(define-fun |B12| () Bool (and |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#2| |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$5!0@1#2| |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$3!0@1#2|))

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
(assert (= (select string.1 (_ bv0 32)) (_ bv103 8)))
(assert (= (select string.1 (_ bv1 32)) (_ bv107 8)))
(assert (= (select string.1 (_ bv2 32)) (_ bv104 8)))
(assert (= (select string.1 (_ bv3 32)) (_ bv105 8)))
(assert (= (cprover.str.len string.1) (_ bv4 32)))
; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$6!0@1#2| () cprover.String string.1)

; find_symbols
(declare-fun |main::1::X!0@1#1| () cprover.String)
; string concatenation
(declare-fun string_concat.2 () cprover.String)
(define-fun string_concat.s0.2 () cprover.String |main::1::X!0@1#1|)
(define-fun string_concat.s1.2 () cprover.String |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$6!0@1#2|)
(assert (forall ((?n cprover.Pos)) (=> (bvult ?n (cprover.str.len string_concat.s0.2)) (= (select string_concat.s0.2 ?n) (select string_concat.2 ?n)))))
(assert (forall ((?n cprover.Pos)) (=> (bvult ?n (cprover.str.len string_concat.s1.2)) (= (select string_concat.s1.2 ?n) (select string_concat.2 (bvadd (cprover.str.len string_concat.s0.2) ?n))))))
(assert (= (cprover.str.len string_concat.2) (bvadd (cprover.str.len string_concat.s0.2) (cprover.str.len string_concat.s1.2))))
(assert (bvuge (cprover.str.len string_concat.2) (cprover.str.len string_concat.s0.2)))
(assert (bvuge (cprover.str.len string_concat.2) (cprover.str.len string_concat.s1.2)))

; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$7!0@1#2| () cprover.String string_concat.2)

; find_symbols
(declare-fun |main::1::Z!0@1#1| () cprover.String)
; string equal
(declare-fun string_equal.3 () Bool)
(define-fun string_equal.s1.3 () cprover.String |main::1::Z!0@1#1|)
(define-fun string_equal.s2.3 () cprover.String |main::$tmp::return_value___CPROVER_uninterpreted_strcat$7!0@1#2|)
(declare-fun string_equal.idx.3 () cprover.Pos)
(assert (=> string_equal.3 (= (cprover.str.len string_equal.s1.3) (cprover.str.len string_equal.s2.3))))
(assert (forall ((?n cprover.Pos)) (=> (and string_equal.3 (bvult ?n (cprover.str.len string_equal.s1.3))) (= (select string_equal.s1.3 ?n) (select string_equal.s2.3 ?n)))))
(assert (=> (not string_equal.3) (or (not (= (cprover.str.len string_equal.s1.3) (cprover.str.len string_equal.s2.3)))
(and (bvult string_equal.idx.3 (cprover.str.len string_equal.s1.3)) (not (= (select string_equal.s1.3 string_equal.idx.3) (select string_equal.s2.3 string_equal.idx.3)))))))

; set_to true
(assert (= |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#2| string_equal.3))

; find_symbols
(declare-fun |main::1::Y1!0@1#1| () cprover.String)
; find_symbols
(declare-fun |main::1::Y2!0@1#1| () cprover.String)
; string concatenation
(declare-fun string_concat.4 () cprover.String)
(define-fun string_concat.s0.4 () cprover.String |main::1::Y1!0@1#1|)
(define-fun string_concat.s1.4 () cprover.String |main::1::Y2!0@1#1|)
(assert (forall ((?n cprover.Pos)) (=> (bvult ?n (cprover.str.len string_concat.s0.4)) (= (select string_concat.s0.4 ?n) (select string_concat.4 ?n)))))
(assert (forall ((?n cprover.Pos)) (=> (bvult ?n (cprover.str.len string_concat.s1.4)) (= (select string_concat.s1.4 ?n) (select string_concat.4 (bvadd (cprover.str.len string_concat.s0.4) ?n))))))
(assert (= (cprover.str.len string_concat.4) (bvadd (cprover.str.len string_concat.s0.4) (cprover.str.len string_concat.s1.4))))
(assert (bvuge (cprover.str.len string_concat.4) (cprover.str.len string_concat.s0.4)))
(assert (bvuge (cprover.str.len string_concat.4) (cprover.str.len string_concat.s1.4)))

; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$4!0@1#2| () cprover.String string_concat.4)

; string equal
(declare-fun string_equal.5 () Bool)
(define-fun string_equal.s1.5 () cprover.String |main::1::Z!0@1#1|)
(define-fun string_equal.s2.5 () cprover.String |main::$tmp::return_value___CPROVER_uninterpreted_strcat$4!0@1#2|)
(declare-fun string_equal.idx.5 () cprover.Pos)
(assert (=> string_equal.5 (= (cprover.str.len string_equal.s1.5) (cprover.str.len string_equal.s2.5))))
(assert (forall ((?n cprover.Pos)) (=> (and string_equal.5 (bvult ?n (cprover.str.len string_equal.s1.5))) (= (select string_equal.s1.5 ?n) (select string_equal.s2.5 ?n)))))
(assert (=> (not string_equal.5) (or (not (= (cprover.str.len string_equal.s1.5) (cprover.str.len string_equal.s2.5)))
(and (bvult string_equal.idx.5 (cprover.str.len string_equal.s1.5)) (not (= (select string_equal.s1.5 string_equal.idx.5) (select string_equal.s2.5 string_equal.idx.5)))))))

; set_to true
(assert (= |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$5!0@1#2| string_equal.5))

(declare-fun string.6 () cprover.String)
(assert (= (select string.6 (_ bv0 32)) (_ bv97 8)))
(assert (= (select string.6 (_ bv1 32)) (_ bv98 8)))
(assert (= (select string.6 (_ bv2 32)) (_ bv99 8)))
(assert (= (select string.6 (_ bv3 32)) (_ bv100 8)))
(assert (= (cprover.str.len string.6) (_ bv4 32)))
; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#2| () cprover.String string.6)

; find_symbols
(declare-fun |main::1::M!0@1#1| () cprover.String)
; string concatenation
(declare-fun string_concat.7 () cprover.String)
(define-fun string_concat.s0.7 () cprover.String |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#2|)
(define-fun string_concat.s1.7 () cprover.String |main::1::M!0@1#1|)
(assert (forall ((?n cprover.Pos)) (=> (bvult ?n (cprover.str.len string_concat.s0.7)) (= (select string_concat.s0.7 ?n) (select string_concat.7 ?n)))))
(assert (forall ((?n cprover.Pos)) (=> (bvult ?n (cprover.str.len string_concat.s1.7)) (= (select string_concat.s1.7 ?n) (select string_concat.7 (bvadd (cprover.str.len string_concat.s0.7) ?n))))))
(assert (= (cprover.str.len string_concat.7) (bvadd (cprover.str.len string_concat.s0.7) (cprover.str.len string_concat.s1.7))))
(assert (bvuge (cprover.str.len string_concat.7) (cprover.str.len string_concat.s0.7)))
(assert (bvuge (cprover.str.len string_concat.7) (cprover.str.len string_concat.s1.7)))

; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$2!0@1#2| () cprover.String string_concat.7)

; string equal
(declare-fun string_equal.8 () Bool)
(define-fun string_equal.s1.8 () cprover.String |main::1::Z!0@1#1|)
(define-fun string_equal.s2.8 () cprover.String |main::$tmp::return_value___CPROVER_uninterpreted_strcat$2!0@1#2|)
(declare-fun string_equal.idx.8 () cprover.Pos)
(assert (=> string_equal.8 (= (cprover.str.len string_equal.s1.8) (cprover.str.len string_equal.s2.8))))
(assert (forall ((?n cprover.Pos)) (=> (and string_equal.8 (bvult ?n (cprover.str.len string_equal.s1.8))) (= (select string_equal.s1.8 ?n) (select string_equal.s2.8 ?n)))))
(assert (=> (not string_equal.8) (or (not (= (cprover.str.len string_equal.s1.8) (cprover.str.len string_equal.s2.8)))
(and (bvult string_equal.idx.8 (cprover.str.len string_equal.s1.8)) (not (= (select string_equal.s1.8 string_equal.idx.8) (select string_equal.s2.8 string_equal.idx.8)))))))

; set_to true
(assert (= |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$3!0@1#2| string_equal.8))

; convert
(define-fun |B13| () Bool (= |main::1::M!0@1#1| |main::1::M!0@1#1|))

; convert
(define-fun |B14| () Bool (= |main::1::X!0@1#1| |main::1::X!0@1#1|))

; convert
(define-fun |B15| () Bool (= |main::1::Y1!0@1#1| |main::1::Y1!0@1#1|))

; convert
(define-fun |B16| () Bool (= |main::1::Y2!0@1#1| |main::1::Y2!0@1#1|))

; convert
(define-fun |B17| () Bool (= |main::1::Z!0@1#1| |main::1::Z!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$6!0@1#1| () cprover.String)
; convert
(define-fun |B18| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$6!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$6!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$7!0@1#1| () cprover.String)
; convert
(define-fun |B19| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_strcat$7!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_strcat$7!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#1| () Bool)
; convert
(define-fun |B20| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$4!0@1#1| () cprover.String)
; convert
(define-fun |B21| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_strcat$4!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_strcat$4!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$5!0@1#1| () Bool)
; convert
(define-fun |B22| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$5!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$5!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#1| () cprover.String)
; convert
(define-fun |B23| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$2!0@1#1| () cprover.String)
; convert
(define-fun |B24| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_strcat$2!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_strcat$2!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$3!0@1#1| () Bool)
; convert
(define-fun |B25| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$3!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$3!0@1#1|))

; set_to true
(assert |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#2|)

; set_to true
(assert |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$5!0@1#2|)

; set_to true
(assert |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$3!0@1#2|)

; convert
(define-fun |B26| () Bool (not |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#2|))

; convert
(define-fun |B27| () Bool (not |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$5!0@1#2|))

; convert
(define-fun |B28| () Bool (not |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$3!0@1#2|))

(check-sat)

(get-value (|B0|))
(get-value (|B1|))
(get-value (|B10|))
(get-value (|B11|))
(get-value (|B12|))
(get-value (|B13|))
(get-value (|B14|))
(get-value (|B15|))
(get-value (|B16|))
(get-value (|B17|))
(get-value (|B18|))
(get-value (|B19|))
(get-value (|B2|))
(get-value (|B20|))
(get-value (|B21|))
(get-value (|B22|))
(get-value (|B23|))
(get-value (|B24|))
(get-value (|B25|))
(get-value (|B26|))
(get-value (|B27|))
(get-value (|B28|))
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
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$4!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$4!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$7!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$7!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_equal$3!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_equal$3!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_equal$5!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_equal$5!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_equal$8!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_literal$6!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_literal$6!0@1#2|))
(get-value (|main::1::M!0@1#1|))
(get-value (|main::1::X!0@1#1|))
(get-value (|main::1::Y1!0@1#1|))
(get-value (|main::1::Y2!0@1#1|))
(get-value (|main::1::Z!0@1#1|))

(exit)
; end of SMT2 file
