; SMT 2
; Generated for CVC 4
(set-info :source "Generated by CBMC 5.4")
(set-option :produce-models true)
(set-logic ALL_SUPPORTED)
; string support via QF_S SMT-LIB logic
(define-sort cprover.String () String)
(define-sort cprover.Char () String)
(define-sort cprover.Pos () (_ BitVec 32))
(define-fun cprover.ubv_to_int ((?x cprover.Pos)) Int (bv2nat ?x))


; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$9!0@1#2| () Bool)
; convert
(define-fun |B0| () Bool |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$9!0@1#2|)

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
(declare-fun array_of.0 () (Array (_ BitVec 32) (_ BitVec 1)))
; set_to true (equal)
(define-fun |__CPROVER_threads_exited#1| () (Array (_ BitVec 32) (_ BitVec 1)) array_of.0)

(define-fun string.1 () cprover.String "a")
; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#2| () cprover.String string.1)

(define-fun string.2 () cprover.String "b")
; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$2!0@1#2| () cprover.String string.2)

; find_symbols
(declare-fun |main::1::Y!0@1#1| () cprover.String)
; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$3!0@1#2| () cprover.String (str.++ |main::1::Y!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$2!0@1#2|))

; find_symbols
(declare-fun |main::1::X!0@1#1| () cprover.String)
; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$4!0@1#2| () cprover.String (str.++ |main::1::X!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_strcat$3!0@1#2|))

; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$5!0@1#2| () cprover.String (str.++ |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#2| |main::$tmp::return_value___CPROVER_uninterpreted_strcat$4!0@1#2|))

(define-fun string.3 () cprover.String "c")
; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$6!0@1#2| () cprover.String string.3)

; find_symbols
(declare-fun |main::1::J!0@1#1| () cprover.String)
; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$7!0@1#2| () cprover.String (str.++ |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$6!0@1#2| |main::1::J!0@1#1|))

; find_symbols
(declare-fun |main::1::I!0@1#1| () cprover.String)
; set_to true (equal)
(define-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$8!0@1#2| () cprover.String (str.++ |main::1::I!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_strcat$7!0@1#2|))

; set_to true
(assert (= |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$9!0@1#2| (= |main::$tmp::return_value___CPROVER_uninterpreted_strcat$5!0@1#2| |main::$tmp::return_value___CPROVER_uninterpreted_strcat$8!0@1#2|)))

; convert
(define-fun |B1| () Bool (= |main::1::I!0@1#1| |main::1::I!0@1#1|))

; convert
(define-fun |B2| () Bool (= |main::1::J!0@1#1| |main::1::J!0@1#1|))

; convert
(define-fun |B3| () Bool (= |main::1::X!0@1#1| |main::1::X!0@1#1|))

; convert
(define-fun |B4| () Bool (= |main::1::Y!0@1#1| |main::1::Y!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#1| () cprover.String)
; convert
(define-fun |B5| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$2!0@1#1| () cprover.String)
; convert
(define-fun |B6| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$2!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$2!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$3!0@1#1| () cprover.String)
; convert
(define-fun |B7| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_strcat$3!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_strcat$3!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$4!0@1#1| () cprover.String)
; convert
(define-fun |B8| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_strcat$4!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_strcat$4!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$5!0@1#1| () cprover.String)
; convert
(define-fun |B9| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_strcat$5!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_strcat$5!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$6!0@1#1| () cprover.String)
; convert
(define-fun |B10| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$6!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_string_literal$6!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$7!0@1#1| () cprover.String)
; convert
(define-fun |B11| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_strcat$7!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_strcat$7!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_strcat$8!0@1#1| () cprover.String)
; convert
(define-fun |B12| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_strcat$8!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_strcat$8!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$9!0@1#1| () Bool)
; convert
(define-fun |B13| () Bool (= |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$9!0@1#1| |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$9!0@1#1|))

; set_to true
(assert |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$9!0@1#2|)

; convert
(define-fun |B14| () Bool (not |main::$tmp::return_value___CPROVER_uninterpreted_string_equal$9!0@1#2|))

(check-sat)

(get-value (|B0|))
(get-value (|B1|))
(get-value (|B10|))
(get-value (|B11|))
(get-value (|B12|))
(get-value (|B13|))
(get-value (|B14|))
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
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$3!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$3!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$4!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$4!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$5!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$5!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$7!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$7!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$8!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_strcat$8!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_equal$9!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_equal$9!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_literal$1!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_literal$2!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_literal$2!0@1#2|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_literal$6!0@1#1|))
(get-value (|main::$tmp::return_value___CPROVER_uninterpreted_string_literal$6!0@1#2|))
(get-value (|main::1::I!0@1#1|))
(get-value (|main::1::J!0@1#1|))
(get-value (|main::1::X!0@1#1|))
(get-value (|main::1::Y!0@1#1|))

(exit)
; end of SMT2 file
